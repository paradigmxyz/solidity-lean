"""Shared cache implementation also used by the standalone importer/driver."""
import importlib.util
from pathlib import Path

_spec = importlib.util.spec_from_file_location(
    "solidity_harness_cache", Path(__file__).resolve().parents[1] / "scripts" / "harness_cache.py")
assert _spec and _spec.loader
_module = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(_module)

digest = _module.digest
key_for = _module.key_for
tool_identity = _module.tool_identity
get = _module.get
put = _module.put
enabled = _module.enabled
