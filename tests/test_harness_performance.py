"""Cache invalidation and native-runner safety checks; no Lean build required."""
import importlib.util
import json
import os
from pathlib import Path
import sys
from dataclasses import replace

import pytest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from contest import env, harness_bridge as hb, measure


def load(name):
    spec = importlib.util.spec_from_file_location(name, ROOT / 'scripts' / (name + '.py'))
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


@pytest.fixture
def cache(tmp_path, monkeypatch):
    monkeypatch.setenv('CONTEST_CACHE_DIR', str(tmp_path / 'cache'))
    monkeypatch.delenv('CONTEST_DISABLE_CACHE', raising=False)
    return load('harness_cache')


def test_cache_isolation_corruption_disable_and_io_failure(cache, tmp_path, monkeypatch):
    key = cache.key_for({'a': 1})
    cache.put('ast', key, {'nodes': [{'x': 1}]})
    hit = cache.get('ast', key)
    hit['nodes'][0]['x'] = 7
    assert cache.get('ast', key)['nodes'][0]['x'] == 1
    assert load('harness_cache').get('ast', key) == {'nodes': [{'x': 1}]}
    disk = tmp_path / 'cache' / 'ast' / (key + '.json')
    entry = json.loads(disk.read_text())
    entry['payload']['nodes'][0]['x'] = 9
    disk.write_text(json.dumps(entry))
    assert cache.get('ast', key, memory=False) is None
    disk.write_text('broken json')
    assert cache.get('ast', key, memory=False) is None
    monkeypatch.setenv('CONTEST_DISABLE_CACHE', '1')
    assert cache.get('ast', key) is None
    monkeypatch.delenv('CONTEST_DISABLE_CACHE')
    blocked = tmp_path / 'not-a-directory'
    blocked.write_text('x')
    monkeypatch.setenv('CONTEST_CACHE_DIR', str(blocked))
    cache.put('ast', key, {'ok': 1})  # cache errors never fail a run
    assert cache.get('ast', key) == {'ok': 1}


def test_failures_are_never_cached(cache):
    calls = []
    def fail():
        calls.append(1)
        raise RuntimeError('compiler failed')
    for _ in range(2):
        with pytest.raises(RuntimeError):
            cache.cached('fail', {}, fail)
    assert len(calls) == 2


def test_ast_reuse_and_input_tool_request_invalidation(tmp_path, monkeypatch, cache):
    importer = load('solc_ast_to_lean_source')
    tool = tmp_path / 'solc'
    tool.write_bytes(b'\x7fELFcompiler version one')
    source = tmp_path / 'C.sol'
    source.write_text('contract C {}')
    calls = []
    def compile_request(solc, request):
        calls.append(request)
        return {'sources': {importer.source_key(source): {'ast': {'nodes': [{'x': 1}]}}}}
    monkeypatch.setattr(importer, '_compile_solc_request', compile_request)
    first = importer.run_solc_ast(str(tool), source)[1]
    first['nodes'][0]['x'] = 10
    for _ in range(15):
        assert importer.run_solc_ast(str(tool), source)[1]['nodes'][0]['x'] == 1
    assert len(calls) == 1
    source.write_text('contract C { uint x; }')
    importer.run_solc_ast(str(tool), source)
    tool.write_bytes(b'\x7fELFcompiler version two')
    importer.run_solc_ast(str(tool), source)
    original = importer.standard_json_input
    def different_settings(path):
        request = original(path)
        request['settings']['evmVersion'] = 'cancun'
        return request
    monkeypatch.setattr(importer, 'standard_json_input', different_settings)
    importer.run_solc_ast(str(tool), source)
    assert len(calls) == 4
    # Imports have an external dependency closure, so are never cached.
    source.write_text('import /* allowed whitespace */ "Dependency.sol"; contract C {}')
    importer.run_solc_ast(str(tool), source)
    importer.run_solc_ast(str(tool), source)
    assert len(calls) == 6


@pytest.mark.parametrize('raw', [
    'ok|0x0011|self=0x1234|origin=0xabcd|evt=t=[1];d=0x12|sto=;0:7',
    'revert|0x1234|self=0x1234|origin=0xabcd|evt=|sto=',
    'deployrevert|0x1234|self=0x1234|origin=0xabcd|evt=|sto=',
])
def test_oracle_reuse_keeps_raw_evidence_and_invalidates(tmp_path, monkeypatch, cache, raw):
    source = tmp_path / 'src' / 'C.sol'
    source.parent.mkdir()
    source.write_text('contract C {}')
    sig = measure.EntrySig('12345678', [], ['uint256'], source, 'C')
    monkeypatch.setattr(measure, 'struct_definitions', lambda *_: {})
    monkeypatch.setattr(measure, 'constructor_param_types', lambda *_: [])
    monkeypatch.setattr(measure.stage_cache, 'get', cache.get)
    monkeypatch.setattr(measure.stage_cache, 'put', cache.put)
    identities = {'forge': 'one', 'solc': 'one'}
    monkeypatch.setattr(measure.stage_cache, 'tool_identity', lambda tool: {'sha256': identities[tool]})
    calls = []
    def run_capture(command, repo, timeout, stdout, stderr):
        calls.append(command)
        (stdout.parent / 'measure_out.txt').write_text(raw)
        return 0
    monkeypatch.setattr(hb._HARNESS, 'run_capture', run_capture)
    def run(n, **kwargs):
        return measure.measure_evm(sig, [], kwargs.pop('ov', env.EnvOverrides()),
                                   tmp_path / str(n), 'forge', 'solc', tmp_path, **kwargs)
    one, status = run(1)
    two, _ = run(2)
    assert status == 'ok' and one is not None and one == two
    assert (tmp_path / '2' / 'measure_out.txt').read_text() == raw
    assert json.loads((tmp_path / '2' / 'oracle-cache.json').read_text())['hit']
    assert len(calls) == 1
    run(3, ov=replace(env.EnvOverrides(), timestamp=999))
    run(4, inject_storage=[(0, 8)])
    run(5, constructor_args=[5])
    source.write_text('contract C { uint a; }')
    run(6)
    identities['forge'] = 'two'
    run(7)
    monkeypatch.setenv('FOUNDRY_OPTIMIZER', 'true')
    run(8)
    assert len(calls) == 7


def test_failed_oracle_cannot_reuse_stale_file(tmp_path, monkeypatch, cache):
    src = tmp_path / 'C.sol'
    src.write_text('contract C {}')
    sig = measure.EntrySig('12345678', [], [], src, 'C')
    work = tmp_path / 'work'
    work.mkdir()
    (work / 'measure_out.txt').write_text('ok|0x|self=0x1234|origin=0xabcd|evt=|sto=')
    monkeypatch.setenv('CONTEST_DISABLE_CACHE', '1')
    monkeypatch.setattr(measure, 'struct_definitions', lambda *_: {})
    monkeypatch.setattr(measure, 'constructor_param_types', lambda *_: [])
    monkeypatch.setattr(hb._HARNESS, 'run_capture', lambda *args: 1)
    result, reason = measure.measure_evm(sig, [], env.EnvOverrides(), work, 'forge', 'solc', tmp_path)
    assert result is None and 'no output' in reason


def test_native_attestation_rejects_stale_source_binary_and_helper(tmp_path, monkeypatch):
    runtime = load('harness_runtime')
    monkeypatch.delenv('CONTEST_NATIVE', raising=False)
    for relative, content in {
        'SpecHuntRunner.lean': 'import SolidCore.Contest.Observable\n',
        'SolidCore/Contest/Observable.lean': '-- helper\n',
        'lakefile.lean': '-- lake\n', 'lake-manifest.json': '{}',
        'lean-toolchain': 'leanprover/lean4:v4.28.0',
        '.lake/build/bin/specHuntRunner': 'binary',
        '.lake/build/lib/lean/SolidCore/Contest/Observable.olean': 'compiled helper',
    }.items():
        path = tmp_path / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(content)
    binary = tmp_path / '.lake/build/bin/specHuntRunner'
    helper = tmp_path / '.lake/build/lib/lean/SolidCore/Contest/Observable.olean'
    stamp = {'sourceSha256': runtime.source_hash(tmp_path),
             'binarySha256': runtime.binary_hash(binary), 'helperSha256': runtime.binary_hash(helper)}
    (binary.parent / 'specHuntRunner.json').write_text(json.dumps(stamp))
    generated = tmp_path / 'case.lean'
    assert runtime.lean_command(tmp_path, 'lake', generated)[2] == str(binary)
    assert runtime.helper_ready(tmp_path)
    monkeypatch.setenv('CONTEST_NATIVE', '0')
    assert runtime.lean_command(tmp_path, 'lake', generated)[2] == 'lean'
    monkeypatch.delenv('CONTEST_NATIVE')
    binary.write_text('different binary')
    assert runtime.lean_command(tmp_path, 'lake', generated)[2] == 'lean'
    binary.write_text('binary')
    helper.write_text('stale helper')
    assert not runtime.helper_ready(tmp_path)
    (tmp_path / 'SolidCore/Contest/Observable.lean').write_text('-- edited semantics')
    assert runtime.lean_command(tmp_path, 'lake', generated)[2] == 'lean'


def test_mutable_tool_wrappers_bypass_caching(cache, tmp_path):
    wrapper = tmp_path / 'solc'
    wrapper.write_text('#!/bin/sh\nexec solc-select "$@"\n')
    assert cache.tool_identity(str(wrapper)) is None


def test_native_failure_fallback_preserves_logs_and_timeout(tmp_path, monkeypatch):
    runtime = load('harness_runtime')
    file = tmp_path / 'case.lean'
    stdout, stderr = tmp_path / 'lean.stdout.log', tmp_path / 'lean.stderr.log'
    monkeypatch.setattr(runtime, 'lean_command', lambda *args: ['lake', 'env', '/native', str(file)])
    times = iter([100.0, 102.9])
    monkeypatch.setattr(runtime.time, 'monotonic', lambda: next(times))
    calls = []
    def capture(command, repo, timeout, out, err):
        calls.append((command, timeout))
        out.write_text('' if len(calls) == 1 else 'original observation')
        err.write_text('Stack overflow' if len(calls) == 1 else '')
        return 134 if len(calls) == 1 else 0
    assert runtime.run_lean_capture(tmp_path, 'lake', file, 10, stdout, stderr, capture) == 0
    assert calls[1] == (['lake', 'env', 'lean', str(file)], 7)
    assert stderr.with_suffix('.native.log').read_text() == 'Stack overflow'
    assert stdout.read_text() == 'original observation'
    assert json.loads((tmp_path / 'native-fallback.json').read_text())['nativeExitStatus'] == 134


def test_native_failure_does_not_extend_exhausted_budget(tmp_path, monkeypatch):
    runtime = load('harness_runtime')
    file = tmp_path / 'case.lean'
    monkeypatch.setattr(runtime, 'lean_command', lambda *args: ['lake', 'env', '/native', str(file)])
    times = iter([100.0, 110.0])
    monkeypatch.setattr(runtime.time, 'monotonic', lambda: next(times))
    calls = []
    def capture(*args):
        calls.append(args)
        return 134
    assert runtime.run_lean_capture(tmp_path, 'lake', file, 10, tmp_path/'out', tmp_path/'err', capture) == 134
    assert len(calls) == 1
