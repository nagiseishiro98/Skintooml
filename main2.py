#!/usr/bin/env python3
"""
Telegram Bot for PUBG Mobile Skin Modification (requests-based fetch)

Replaces aiohttp with requests. Uses run_in_executor for blocking network calls.
"""

import os
import io
import re
import zlib
import gzip
import shutil
import tempfile
import logging
import asyncio
import requests
from pathlib import Path
from typing import Dict, Optional, Tuple, List
from functools import wraps
from telegram import Update
from telegram.ext import Application, CommandHandler, ContextTypes

# ==========================
# Configuration via env vars
# ==========================
BOT_TOKEN = os.getenv("BOT_TOKEN", "").strip()
GITHUB_PAK_URL = os.getenv("GITHUB_PAK_URL", "").strip()
GITHUB_DUMP_URL = os.getenv("GITHUB_DUMP_URL", "").strip()

WINDOW_SIZE = 20
MARKER_BYTES = b'\xff\xff\xff'
MIN_NULL_BYTES = 3
MIN_RESULT_SIZE = 32
MAX_OFFSET_TRY = 8

SIG2KEY = {
    bytes.fromhex("9DC7"): bytes.fromhex("E55B4ED1"),
    bytes.fromhex("9D81"): bytes.fromhex("E51D4ED1"),
}

MAGIC_EXT = {
    0x9e2a83c1: ".uasset",
    0x61754c1b: ".lua",
    0x090a0d7b: ".dat",
    0x007bfeff: ".dat",
    0x200a0d7b: ".dat",
    0x27da0020: ".res",
    0x00000001: ".res",
    0x7bbfbbef: ".res",
    0x44484b42: ".bnk",
}

ZLIB_HEADERS = [b"\x78\x01", b"\x78\x5E", b"\x78\x9C", b"\x78\xDA"]
GZIP_HEADER = b"\x1F\x8B"

user_sessions: Dict[int, Dict] = {}

logging.basicConfig(format="%(asctime)s - %(levelname)s - %(message)s", level=logging.INFO)
logger = logging.getLogger("skinmod-bot")

# Global cache for PAK and dump files (fetched once per bot runtime)
global_pak_data = None
global_dump_content = None
cache_lock = asyncio.Lock()

# Semaphore limits concurrent heavy ops globally
MAX_CONCURRENT_PROCESSING = 2
processing_semaphore = asyncio.Semaphore(MAX_CONCURRENT_PROCESSING)

def limit_concurrency(func):
    @wraps(func)
    async def wrapper(update, context, *args, **kwargs):
        async with processing_semaphore:
            return await func(update, context, *args, **kwargs)
    return wrapper

class SkinModProcessor:

    def __init__(self, work_dir: str):
        self.work_dir = Path(work_dir)
        self.source_dir = self.work_dir / "source"
        self.result_dir = self.work_dir / "result"
        self.cache_dir = self.work_dir / "cache"
        for d in [self.source_dir, self.result_dir, self.cache_dir]:
            d.mkdir(parents=True, exist_ok=True)
        self.id_to_hex_map: Dict[str, str] = {}
        self.modified_files = set()

    def load_dump_data(self, dump_content: str) -> None:
        self.id_to_hex_map = {}
        for line in dump_content.strip().splitlines():
            line = line.strip()
            if not line or "|" not in line:
                continue
            a, b, *rest = [p.strip() for p in line.split("|")]
            if a and b:
                self.id_to_hex_map[a] = b.upper()

    @staticmethod
    def is_sig_at(data: bytes, i: int) -> Optional[bytes]:
        if i + 2 > len(data):
            return None
        return SIG2KEY.get(data[i:i+2], None)

    def xor_decode_with_feedback(self, data: bytes) -> bytes:
        out = bytearray()
        key = None
        seg_pos = 0
        seg_start_out = 0
        i = 0
        while i < len(data):
            k = self.is_sig_at(data, i)
            if k is not None:
                key = k
                seg_pos = 0
                seg_start_out = len(out)
            if key is not None:
                if seg_pos < 4:
                    o = data[i] ^ key[seg_pos]
                else:
                    fb_index = seg_start_out + (seg_pos - 4)
                    o = data[i] ^ out[fb_index]
                out.append(o)
                seg_pos += 1
            else:
                out.append(data[i])
            i += 1
        return bytes(out)

    def xor_reencode_from_original(self, encoded_original: bytes, decoded_modified: bytes) -> bytes:
        assert len(encoded_original) == len(decoded_modified)
        out_enc = bytearray()
        key = None
        seg_pos = 0
        seg_start_out = 0
        for i in range(len(decoded_modified)):
            k = self.is_sig_at(encoded_original, i)
            if k is not None:
                key = k
                seg_pos = 0
                seg_start_out = i
            if key is not None:
                if seg_pos < 4:
                    b = decoded_modified[i] ^ key[seg_pos]
                else:
                    fb_index = seg_start_out + (seg_pos - 4)
                    b = decoded_modified[i] ^ decoded_modified[fb_index]
                out_enc.append(b)
                seg_pos += 1
            else:
                out_enc.append(decoded_modified[i])
        return bytes(out_enc)

    @staticmethod
    def is_valid_zlib_header(b1: int, b2: int) -> bool:
        if (b1 & 0x0F) != 8:
            return False
        cmf_flg = (b1 << 8) | b2
        return (cmf_flg % 31) == 0

    def guess_extension(self, blob: bytes) -> str:
        if len(blob) < 4:
            return ".uexp"
        magic = int.from_bytes(blob[:4], "little")
        return MAGIC_EXT.get(magic, ".uexp")

    def try_decompress_at(self, buf: bytes, start: int, max_offset: int = MAX_OFFSET_TRY) -> Optional[Dict]:
        length = len(buf)
        modes = [('zlib', 15), ('gzip', 31)]
        for ofs in range(0, max_offset + 1):
            s = start + ofs
            if s >= length - 2:
                break
            for mode_name, wbits in modes:
                if mode_name == 'zlib':
                    b1 = buf[s]
                    if b1 != 0x78:
                        continue
                    b2 = buf[s + 1]
                    if not self.is_valid_zlib_header(b1, b2):
                        continue
                if mode_name == 'gzip':
                    if s + 1 >= length:
                        continue
                    if not (buf[s] == 0x1F and buf[s + 1] == 0x8B):
                        continue
                try:
                    d = zlib.decompressobj(wbits)
                    res = d.decompress(buf[s:])
                    res += d.flush()
                    consumed = len(buf[s:]) - len(d.unused_data)
                    if not d.eof or consumed <= 0 or res is None or len(res) < MIN_RESULT_SIZE:
                        continue
                    return {"result": res, "consumed": consumed, "mode": mode_name, "ofs": ofs}
                except Exception:
                    continue
        return None

    def scan_and_extract_smart(self, data: bytes) -> Tuple[int, List[Dict]]:
        count = 0
        pos = 0
        length = len(data)
        entries: List[Dict] = []

        def find_next_candidate(p):
            idxs = []
            i = data.find(b"\x78", p)
            if i != -1:
                idxs.append(i)
            j = data.find(GZIP_HEADER, p)
            if j != -1:
                idxs.append(j)
            return min(idxs) if idxs else -1

        while True:
            cand = find_next_candidate(pos)
            if cand == -1 or cand >= length - 2:
                break
            trial = self.try_decompress_at(data, cand, MAX_OFFSET_TRY)
            if trial:
                res = trial["result"]
                consumed = trial["consumed"]
                ofs = trial["ofs"]
                count += 1
                ext = self.guess_extension(res)
                fname = f"{count:06d}{ext}"
                outpath = self.source_dir / fname
                outpath.write_bytes(res)
                start_pos = cand + ofs
                entries.append({
                    "index": count,
                    "start": start_pos,
                    "consumed": consumed,
                    "filename": fname,
                    "ext": ext,
                    "mode": trial["mode"]
                })
                pos = start_pos + consumed
            else:
                pos = cand + 1
        return count, entries

    def compress_by_mode(self, raw_bytes: bytes, mode: str) -> bytes:
        if mode == "zlib":
            return zlib.compress(raw_bytes, level=9)
        elif mode == "gzip":
            bio = io.BytesIO()
            with gzip.GzipFile(fileobj=bio, mode="wb") as gzf:
                gzf.write(raw_bytes)
            return bio.getvalue()
        return zlib.compress(raw_bytes, level=9)

    def search_for_pattern_in_dir(self, pattern_bytes: bytes, directory: Path) -> Dict[str, List[int]]:
        found_files: Dict[str, List[int]] = {}
        for file_path in directory.rglob("*"):
            if file_path.is_file():
                try:
                    data = file_path.read_bytes()
                    offsets = []
                    idx = data.find(pattern_bytes)
                    while idx != -1:
                        offsets.append(idx)
                        idx = data.find(pattern_bytes, idx + 1)
                    if offsets:
                        found_files[str(file_path)] = offsets
                except Exception:
                    continue
        return found_files

    def enhanced_marker_validation(self, file_path: str, found_offset: int, min_null_bytes: int = MIN_NULL_BYTES) -> Optional[int]:
        try:
            with open(file_path, "rb") as f:
                data = f.read(found_offset)
        except Exception:
            return None
        positions = [m.start() for m in re.finditer(re.escape(MARKER_BYTES), data)]
        if not positions:
            return None
        for pos in reversed(positions):
            for null_count in range(1, 5):
                null_start = pos - null_count
                if null_start < 0:
                    continue
                preceding_bytes = data[null_start:pos]
                null_byte_count = sum(1 for b in preceding_bytes if b == 0)
                if null_byte_count >= len(preceding_bytes) // 2:
                    return pos
        return positions[-1] if positions else None

    def advanced_filter_files(self, orig_files: Dict[str, List[int]]) -> Dict[str, List[int]]:
        if not orig_files:
            return {}

        if len(orig_files) == 1:
            return orig_files

        single_occurrence_files = {f: o for f, o in orig_files.items() if len(o) == 1}

        if not single_occurrence_files:
            min_occurrences = min(len(offsets) for offsets in orig_files.values())
            single_occurrence_files = {f: o for f, o in orig_files.items() if len(o) == min_occurrences}

        valid_files = {}
        for file_path, offsets in single_occurrence_files.items():
            offset = offsets[0]
            marker_offset = self.enhanced_marker_validation(file_path, offset)
            if marker_offset is None:
                continue
            gap = offset - (marker_offset + len(MARKER_BYTES))
            if gap < 0:
                continue
            valid_files[file_path] = {
                'offsets': offsets,
                'marker_gap': gap,
                'marker_offset': marker_offset,
            }

        if not valid_files:
            first_file = list(orig_files.items())[0]
            return {first_file[0]: first_file[1]}

        best_file = min(valid_files.items(), key=lambda x: x[1]['marker_gap'])
        return {best_file[0]: best_file[1]['offsets']}

    def compute_replacement_index(self, file_path: str, marker_offset: int) -> Tuple[Optional[str], Optional[int]]:
        if marker_offset is None:
            return None, None
        base = marker_offset - len(MARKER_BYTES)
        start = max(0, base - WINDOW_SIZE)
        try:
            data = Path(file_path).read_bytes()
        except Exception:
            return None, None
        if len(data) <= base:
            return None, None
        window = data[start:base + 1]
        nonzero_pos = None
        for i in range(len(window) - 1, -1, -1):
            if window[i] != 0:
                nonzero_pos = start + i
                break
        if nonzero_pos is None:
            return None, None
        if nonzero_pos - 1 >= 0 and nonzero_pos - 1 < len(data) and data[nonzero_pos - 1] != 0:
            repl_offset = nonzero_pos - 1
            if nonzero_pos + 1 >= len(data):
                return None, None
            index_bytes = data[nonzero_pos - 1: nonzero_pos + 1]
        else:
            repl_offset = nonzero_pos
            if nonzero_pos + 2 >= len(data):
                return None, None
            index_bytes = data[nonzero_pos: nonzero_pos + 2]
        if len(index_bytes) < 2:
            return None, None
        return index_bytes.hex().upper(), repl_offset

    def apply_patch_to_file(self, file_path: str, offset: int, new_bytes: bytes) -> Optional[str]:
        try:
            with open(file_path, "r+b") as f:
                f.seek(offset)
                f.write(new_bytes)
                f.flush()
            return file_path
        except Exception:
            return None

    def edit_hex_value(self, original_hex: str, new_hex: str) -> bool:
        try:
            orig_pattern = bytes.fromhex(original_hex)
            new_pattern = bytes.fromhex(new_hex)
        except ValueError:
            return False

        orig_files: Dict[str, List[int]] = self.search_for_pattern_in_dir(orig_pattern, self.source_dir)
        if not orig_files:
            return False

        new_files: Dict[str, List[int]] = self.search_for_pattern_in_dir(new_pattern, self.source_dir)
        if not new_files:
            return False

        filtered_files = self.advanced_filter_files(orig_files)
        if not filtered_files:
            return False

        any_changed = False
        for orig_file_path, orig_offsets in filtered_files.items():
            file_basename = os.path.basename(orig_file_path)
            dest_path = self.result_dir / file_basename

            best_new_index = None
            best_gap = None
            for new_file_path, new_offsets in new_files.items():
                for new_found_offset in new_offsets:
                    new_marker = self.enhanced_marker_validation(new_file_path, new_found_offset)
                    if new_marker is None:
                        continue
                    new_index, _ = self.compute_replacement_index(new_file_path, new_marker)
                    if new_index is None:
                        continue
                    gap = new_found_offset - (new_marker + len(MARKER_BYTES))
                    if gap < 0:
                        continue
                    if best_gap is None or gap < best_gap:
                        best_gap = gap
                        best_new_index = new_index

            if best_new_index is None:
                continue

            file_will_be_modified = False
            patches_to_apply = []
            new_bytes = bytes.fromhex(best_new_index)

            for orig_found_offset in orig_offsets:
                orig_marker = self.enhanced_marker_validation(orig_file_path, orig_found_offset)
                if orig_marker is None:
                    continue
                orig_index, orig_repl_offset = self.compute_replacement_index(orig_file_path, orig_marker)
                if orig_index is None:
                    continue
                patch_already_applied = False
                if dest_path.exists():
                    try:
                        with open(dest_path, "rb") as f:
                            f.seek(orig_repl_offset)
                            current_bytes = f.read(len(new_bytes))
                            if current_bytes == new_bytes:
                                patch_already_applied = True
                                file_will_be_modified = True
                    except:
                        pass
                if not patch_already_applied:
                    patches_to_apply.append((orig_repl_offset, orig_index, best_new_index, new_bytes))

            if not dest_path.exists() and (patches_to_apply or file_will_be_modified):
                try:
                    shutil.copy2(orig_file_path, dest_path)
                    file_will_be_modified = True
                except Exception:
                    continue
            elif dest_path.exists():
                file_will_be_modified = True

            if patches_to_apply:
                try:
                    with open(dest_path, "r+b") as f:
                        for patch_offset, orig_idx, new_idx, patch_bytes in patches_to_apply:
                            f.seek(patch_offset)
                            f.write(patch_bytes)
                            f.flush()
                        os.fsync(f.fileno())
                    any_changed = True
                except Exception:
                    pass

            if file_will_be_modified:
                self.modified_files.add(file_basename)
            any_changed = True

        return any_changed

    def process_skin_modifications(self, id_pairs: List[Tuple[str, str]]) -> int:
        modified_count = 0
        for orig_val, new_val in id_pairs:
            if orig_val.isdigit() and orig_val in self.id_to_hex_map:
                orig_val = self.id_to_hex_map[orig_val]
            if new_val.isdigit() and new_val in self.id_to_hex_map:
                new_val = self.id_to_hex_map[new_val]
            orig_val = orig_val.upper()
            new_val = new_val.upper()
            if self.edit_hex_value(orig_val, new_val):
                modified_count += 1
        return modified_count

    def repack_pak(self, original_pak_data: bytes, manifest: Dict) -> bytes:
        decoded_orig = self.xor_decode_with_feedback(original_pak_data)
        decoded = bytearray(decoded_orig)
        entries = manifest.get("entries", [])
        repacked_count = 0

        for e in entries:
            filename = e["filename"]
            start = int(e["start"])
            consumed = int(e["consumed"])
            mode = e.get("mode", "zlib")
            result_file_path = self.result_dir / filename
            if result_file_path.exists():
                raw = result_file_path.read_bytes()
                comp = self.compress_by_mode(raw, mode)
                if len(comp) <= consumed:
                    decoded[start:start + len(comp)] = comp
                    if len(comp) < consumed:
                        decoded[start + len(comp):start + consumed] = b"\x00" * (consumed - len(comp))
                    repacked_count += 1
        encoded_final = self.xor_reencode_from_original(original_pak_data, bytes(decoded))
        return encoded_final

# ----------------------------
# Helper functions...
# ----------------------------

def fetch_bytes_sync(url: str, timeout: int = 60) -> bytes:
    """Blocking fetch using requests. Use from executor."""
    r = requests.get(url, timeout=timeout, stream=False)
    r.raise_for_status()
    return r.content

def parse_skin_pairs_from_message(text: str, args: List[str]) -> List[Tuple[str, str]]:
    pairs: List[Tuple[str, str]] = []
    if "\n" in text:
        lines = [ln.strip() for ln in text.splitlines()]
        if lines and lines[0].startswith("/skin"):
            lines = lines[1:]
        for ln in lines:
            if not ln:
                continue
            if ',' not in ln:
                continue
            a, b = ln.split(',', 1)
            a = a.strip()
            b = b.strip()
            if a and b:
                pairs.append((a, b))
    else:
        for pair_str in (args or []):
            if ',' not in pair_str:
                continue
            a, b = pair_str.split(',', 1)
            a = a.strip()
            b = b.strip()
            if a and b:
                pairs.append((a, b))
    return pairs

# ----------------------------
# Command Handlers...
# ----------------------------

async def start(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    uid = update.effective_user.id
    if uid not in user_sessions:
        user_sessions[uid] = {
            'work_dir': None,
            'processor': None,
            'pak_data': None,
            'manifest': None,
            'ready': False
        }
    await update.message.reply_text(
        "🔥 BGMI Skin Mod Bot (requests) \n\n"
        "Commands:\n"
        "/unpack - Unpack First\n"
        "/skin - Modify skins (multiline or args pairs supported)\n"
        "/reset - Reset session\n\n"
        "Flow: run /unpack once, then /skin as many times as needed."
    )

async def reset(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    uid = update.effective_user.id
    sess = user_sessions.get(uid)
    if sess and sess.get('work_dir'):
        shutil.rmtree(sess['work_dir'], ignore_errors=True)
    user_sessions[uid] = {
        'work_dir': None,
        'processor': None,
        'pak_data': None,
        'manifest': None,
        'ready': False
    }
    await update.message.reply_text("🔁 Session reset. Use /unpack to start again.")

@limit_concurrency
async def unpack(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    global global_pak_data, global_dump_content
    uid = update.effective_user.id

    if not GITHUB_PAK_URL or not GITHUB_DUMP_URL:
        await update.message.reply_text("❌ Server misconfigured: missing GITHUB_PAK_URL or GITHUB_DUMP_URL.")
        return

    async with cache_lock:
        if global_pak_data is None or global_dump_content is None:
            await update.message.reply_text("⬇️ Fetching files, please wait...")
            try:
                loop = asyncio.get_running_loop()
                pak_bytes_fut = loop.run_in_executor(None, fetch_bytes_sync, GITHUB_PAK_URL)
                dump_bytes_fut = loop.run_in_executor(None, fetch_bytes_sync, GITHUB_DUMP_URL)
                pak_bytes, dump_bytes = await asyncio.gather(pak_bytes_fut, dump_bytes_fut)
                global_pak_data = pak_bytes
                global_dump_content = dump_bytes.decode('utf-8', errors='ignore')
            except Exception as e:
                await update.message.reply_text(f"❌ Failed to fetch files: {e}")
                return

    sess = user_sessions.get(uid, {})
    if sess.get('work_dir') is None:
        work_dir = tempfile.mkdtemp(prefix=f"skinmod_{uid}_")
        sess['work_dir'] = work_dir
    else:
        work_dir = sess['work_dir']

    processor = SkinModProcessor(work_dir)
    processor.load_dump_data(global_dump_content)

    await update.message.reply_text("🔓 Unpacking PAK... (this may take some time)")

    loop = asyncio.get_running_loop()
    decoded_data = await loop.run_in_executor(None, processor.xor_decode_with_feedback, global_pak_data)
    count, entries = await loop.run_in_executor(None, processor.scan_and_extract_smart, decoded_data)

    sess.update({
        'processor': processor,
        'pak_data': global_pak_data,
        'manifest': {"total": count, "entries": entries},
        'ready': True
    })
    user_sessions[uid] = sess

    await update.message.reply_text(
        f"✅ Unpack complete \n"
        f"📊 Extracted: {count} files\n"
        f"📋 Loaded mappings: {len(processor.id_to_hex_map)}\n"
        "Now send /skin with pairs, e.g.:\n/skin\n1400101,403042\n1400122,404031"
    )

@limit_concurrency
async def skin(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    uid = update.effective_user.id
    sess = user_sessions.get(uid)

    if not sess or not sess.get('ready'):
        await update.message.reply_text("❌ Not ready. Run /unpack first.")
        return

    try:
        processor: SkinModProcessor = sess['processor']
        full_text = update.message.text or ""
        pairs = parse_skin_pairs_from_message(full_text, context.args)
        pairs = [tuple(pair) for pair in pairs]
        if not pairs:
            await update.message.reply_text(
                "❌ Invalid format.\n\n"
                "📝 Examples:\n"
                "/skin\n1400101,403042\n1400122,404031\n\n"
                "Or: /skin 1400101,403042 1400122,404031"
            )
            return

        await update.message.reply_text(f"🔄 Processing {len(pairs)} pair(s) with advanced filtering...")

        loop = asyncio.get_running_loop()
        modified_count = await loop.run_in_executor(None, processor.process_skin_modifications, pairs)
        total_modified_files = len(processor.modified_files)

        if modified_count == 0:
            await update.message.reply_text(
                "⚠️ No modifications applied.\n\n"
                "🔍 Possible reasons:\n"
                "• IDs not found in dump.txt\n"
                "• Patterns not found in PAK files\n"
                "• Advanced filtering excluded files\n"
                "• Null bytes validation failed\n\n"
                "💡 Try different ID pairs or check dump.txt mapping."
            )
            return

        await update.message.reply_text("📦 Hold on. We are delivering You")

        original_pak = sess['pak_data']
        manifest = sess['manifest']
        modified_pak = await loop.run_in_executor(None, processor.repack_pak, original_pak, manifest)

        out_path = Path(processor.work_dir) / "modified.pak"
        out_path.write_bytes(modified_pak)

        with open(out_path, "rb") as f:
            await context.bot.send_document(
                chat_id=update.effective_chat.id,
                document=f,
                filename="game_patch_modified.pak",
                caption=(
                    f"🔥 Enhanced Skin Mod PAK\n\n"
                    f"✅ Applied: {modified_count} modifications\n"
                    f"📁 Files modified: {total_modified_files}\n"
                    f"📏 Size: {len(modified_pak) / (1024*1024):.1f}MB\n\n"
                    f"Ready to use! 🚀"
                ),
            )

        await update.message.reply_text(
            f"✅ Success with enhanced filtering!\n\n"
            f"📊 Statistics:\n"
            f"• Modifications applied: {modified_count}\n"
            f"• Files modified: {total_modified_files}\n"
            f"• Multi-patch support: Enabled\n\n"
            f"💡 Tip: Send /skin again to make more changes, or /reset to start fresh."
        )
    except Exception as e:
        logger.exception("Skin error")
        await update.message.reply_text(f"❌ Error: {e}")

def main():
    if not BOT_TOKEN:
        print("❌ Set BOT_TOKEN env var")
        return
    if not GITHUB_PAK_URL or not GITHUB_DUMP_URL:
        print("⚠️ Set GITHUB_PAK_URL and GITHUB_DUMP_URL env vars")
    app = Application.builder().token(BOT_TOKEN).build()
    app.add_handler(CommandHandler("start", start))
    app.add_handler(CommandHandler("help", start))
    app.add_handler(CommandHandler("reset", reset))
    app.add_handler(CommandHandler("unpack", unpack))
    app.add_handler(CommandHandler("skin", skin))
    print("🚀 Enhanced Skin Mod Bot (requests) started!")
    app.run_polling(close_loop=False)

if __name__ == "__main__":
    main()
