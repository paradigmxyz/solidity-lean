"""Content-addressed caches for deterministic, engine-independent harness stages.

Persistent caching is opt-in via CONTEST_CACHE_DIR. Keep this directory outside
submission sandboxes. CONTEST_DISABLE_CACHE=1 bypasses both memory and disk.
Failures are never stored. Cached JSON is decoded afresh to prevent AST mutation
in one consumer from changing another consumer's input.
"""
from __future__ import annotations
import hashlib
import json
import os
from pathlib import Path
import shutil
import tempfile
from collections import OrderedDict
from functools import lru_cache
from threading import RLock
from typing import Any, Callable

_SCHEMA = 1
_MAX_ENTRY = 32 * 1024 * 1024
_MEMORY: OrderedDict[tuple[str, str], bytes] = OrderedDict()
_MEMORY_BYTES = 0
_LOCK = RLock()


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def encode(value: Any) -> bytes:
    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=False).encode()


@lru_cache(maxsize=64)
def _tool_hash(path: str, metadata: tuple) -> str:
    h = hashlib.sha256()
    with open(path, "rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def tool_identity(command: str) -> dict | None:
    """Identify a native executable; mutable wrappers deliberately bypass caching."""
    resolved = shutil.which(command) if "/" not in command else command
    if not resolved:
        return None
    path = Path(resolved).resolve()
    try:
        st = path.stat()
        with path.open("rb") as executable:
            magic = executable.read(4)
        if magic not in (b"\x7fELF", b"\xcf\xfa\xed\xfe", b"\xce\xfa\xed\xfe",
                         b"\xfe\xed\xfa\xcf", b"\xfe\xed\xfa\xce",
                         b"\xca\xfe\xba\xbe", b"\xbe\xba\xfe\xca") and magic[:2] != b"MZ":
            return None
        metadata = (st.st_dev, st.st_ino, st.st_size, st.st_mtime_ns, st.st_ctime_ns)
        return {"path": str(path), "sha256": _tool_hash(str(path), metadata)}
    except OSError:
        return None


def enabled() -> bool:
    return os.environ.get("CONTEST_DISABLE_CACHE") != "1"


def key_for(inputs: Any) -> str:
    return digest(encode({"schema": _SCHEMA, "inputs": inputs}))


def _path(namespace: str, key: str) -> Path | None:
    root = os.environ.get("CONTEST_CACHE_DIR")
    return Path(root).expanduser() / namespace / (key + ".json") if root else None


def get(namespace: str, key: str, *, memory: bool = True) -> Any | None:
    if not enabled():
        return None
    if memory:
        with _LOCK:
            raw = _MEMORY.get((namespace, key))
            if raw is not None:
                _MEMORY.move_to_end((namespace, key))
                return json.loads(raw)
    path = _path(namespace, key)
    if path is None:
        return None
    try:
        if path.stat().st_size > _MAX_ENTRY:
            return None
        entry = json.loads(path.read_bytes())
        if entry["schema"] != _SCHEMA or entry["key"] != key:
            return None
        payload = entry["payload"]
        if digest(encode(payload)) != entry["sha256"]:
            return None
        return payload
    except (OSError, ValueError, KeyError, TypeError):
        return None


def put(namespace: str, key: str, payload: Any, *, memory: bool = True) -> None:
    global _MEMORY_BYTES
    if not enabled():
        return
    raw = encode(payload)
    if len(raw) > _MAX_ENTRY // 2:
        return
    if memory:
        with _LOCK:
            previous = _MEMORY.pop((namespace, key), None)
            if previous is not None:
                _MEMORY_BYTES -= len(previous)
            _MEMORY[(namespace, key)] = raw
            _MEMORY_BYTES += len(raw)
            while len(_MEMORY) > 64 or _MEMORY_BYTES > _MAX_ENTRY:
                _, old = _MEMORY.popitem(last=False)
                _MEMORY_BYTES -= len(old)
    path = _path(namespace, key)
    if path is None:
        return
    temporary = None
    try:
        path.parent.mkdir(parents=True, exist_ok=True, mode=0o700)
        entry = {"schema": _SCHEMA, "key": key, "sha256": digest(raw), "payload": payload}
        with tempfile.NamedTemporaryFile(dir=path.parent, mode="wb", delete=False) as out:
            temporary = Path(out.name)
            out.write(encode(entry))
        os.replace(temporary, path)
    except OSError:
        # A full/unavailable cache must not change adjudication outcomes.
        pass
    finally:
        if temporary is not None:
            try:
                temporary.unlink(missing_ok=True)
            except OSError:
                pass


def cached(namespace: str, inputs: Any, compute: Callable[[], Any]) -> Any:
    key = key_for(inputs)
    hit = get(namespace, key)
    if hit is not None:
        return hit
    value = compute()  # exceptions intentionally bypass publication
    put(namespace, key, value)
    return value
