#!/usr/bin/env python3
"""Write the refinement proof modules of one corpus contract.

    gen_proof.py NAME MODULE SOLAR_JSON SOLC_AST_JSON SOURCE

SOLAR_JSON is solar's --emit abi,hashes output for the contract and
SOLC_AST_JSON solc's --combined-json ast output, which names the members of
each enum. The script writes, under SolidCore/Refinement/Corpus/:

  MODULE/Defs.lean      the code, the checked contract, its functions, the scope
  MODULE/PartI.lean     one native_decide check of every PARTS-th call
  MODULE/Dirty.lean     EthLib rejects every dirty argument word (symbolic, dirty_symex)
  MODULE.lean           the refinement theorems: on clean words, then on every word
  MODULE/SeqStates.lean the storages clean calls reach, found by Seq.explore
  MODULE/SeqDefs.lean   the sequence certificate and its dirty-call check
  MODULE/SeqPartI.lean  one native_decide check of every PARTS-th certificate call
  MODULE/Seq.lean       the refinement on sequences of calls

and SolidCore/Refinement/Seq/Corpus.lean, which imports every MODULE/Seq.lean.
For a contract with a function that is neither pure nor view, the sequence
certificate comes from running SolidCore.Refinement.Seq.explore through lake,
so MODULE/Defs.lean must build.

Every parameter must have a small ABI type (uintN or intN with N <= 16, bool or
an enum): the scope is every call with clean argument words, so it must be
finite and small. A contract with a wide parameter (uintN or intN with N > 16,
address or bytesN) instead gets a symbolic proof, written by gen_wide below into
MODULE.lean alone: SolidCore's interpreter and solar's bytecode both run on free
argument words (SolidCore.Refinement.Wide). It needs the contract's constructor to
leave no storage and no logs, and a function that is not pure or view to write at
most one slot on each path. It builds SolidCore.Refinement.Source.MODULE with lake
and prints SolidCore's core contract through Lean, which the proof checks against
SolidCore's own in the kernel (kernel_rfl, below). A contract with any other parameter gets no
proof, and the script says so and exits 3.

A contract with a dynamic or struct parameter (bytes, an array of a small type, a
struct of small types) gets a proof on SolidCore.Refinement.Dyn.dynScope, written by
gen_dyn: MODULE/Defs.lean and MODULE/PartI.lean check every canonical encoding within
the bounds by native_decide, MODULE/Malformed.lean proves EthLib rejects malformed call
data by dyn_symex, and MODULE.lean states refines_full. A line
"// refinement: bytes=N array=M" sets the bounds on the length of a bytes argument and
of an array (default 2 each).

A line "// refinement: fuel=N" in the source sets SolidCore's fuel (default 4096).
Every symbolic proof learns that SolidCore's checked core is the printed literal coreLit
by one kernel conversion check (kernel_rfl shape_eq, SolidCore.Refinement.KernelRfl), on
copies of the type checker that read each function's selector from a table
(selectorTable): selector_eq, from one kernel_rfl check of each selector by Keccak-256
against the bytecode file's, which solc's AST functionSelector confirms. No Bool
recognizer of coreLit is generated: its match on the whole literal and split cost
gigabytes. "// refinement: shape=kernel" also proves a small symbolic contract's dirty
shapeOk in the kernel; without it, that check is native_decide.
gen.sh reads "// refinement: solar-flags=F1,F2" and passes the flags to solar.
"""
import json
import math
import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path

CALLS_PER_PART = 4096
MAX_CALLS = 1 << 17

name, module, solar_json, ast_json, source = sys.argv[1:]
contracts = json.loads(Path(solar_json).read_text())["contracts"]
main = next(c for k, c in contracts.items() if k.rsplit(":", 1)[1] == "Main")
abi = main["abi"]
if isinstance(abi, str):
    abi = json.loads(abi)

enums = {}
for unit in json.loads(Path(ast_json).read_text())["sources"].values():
    stack = [unit["AST"]]
    while stack:
        node = stack.pop()
        if isinstance(node, dict):
            if node.get("nodeType") == "EnumDefinition":
                enums[node["canonicalName"]] = len(node["members"])
            stack.extend(node.values())
        elif isinstance(node, list):
            stack.extend(node)

fuel = 4096
m = re.search(r"//\s*refinement:\s*fuel=(\d+)", Path(source).read_text())
if m:
    fuel = int(m.group(1))

# "// refinement: shape=kernel" has the kernel check a small symbolic contract's dirty shapeOk
# (kernel_rfl) instead of native_decide. Every contract's core shape is the kernel's.
kernel_shape = re.search(r"//\s*refinement:.*\bshape=kernel\b", Path(source).read_text()) is not None
# A certified contract (REFINEMENT_CERTIFIED=1, which gen.sh sets for the names in
# scripts/refinement/certified) must be proved by the kernel alone: no native_decide or
# bv_decide fallback, so it needs "// refinement: shape=kernel". gen.sh then checks the
# written modules with scripts/refinement/kernel_only.py.
if os.environ.get("REFINEMENT_CERTIFIED") == "1" and not kernel_shape:
    sys.exit(f"{source}: a certified contract needs '// refinement: shape=kernel'; without it "
             "the shape check falls back to native_decide")


# Each function's selector as solc's AST gives it (functionSelector), by name, for the
# contract Main: the check of solar's signatures in selector_block.
solc_selectors = {}
for unit in json.loads(Path(ast_json).read_text())["sources"].values():
    for node in unit["AST"].get("nodes", []):
        if node.get("nodeType") == "ContractDefinition" and node.get("name") == "Main":
            for member in node.get("nodes", []):
                if "functionSelector" in member:
                    solc_selectors[member["name"]] = member["functionSelector"]


def param(p):
    internal = p.get("internalType", "")
    if internal.startswith("enum "):
        n = enums[internal[len("enum "):]]
        return f"(.enum {n})", n
    t = p["type"]
    if t == "bool":
        return ".bool", 2
    m = re.fullmatch(r"(u?)int(\d+)", t)
    if m and int(m.group(2)) <= 16:
        bits = int(m.group(2))
        return f"(.{'uint' if m.group(1) else 'int'} {bits})", 2 ** bits
    return None, None


def wide_param(p):
    """The Abi.Param a wide parameter is counted as, or None. Abi.fullScope only counts
    a function's parameters, so a wide one stands for every word below 2 ^ 256."""
    t = p["type"]
    m = re.fullmatch(r"(u?)int(\d+)", t)
    if m and int(m.group(2)) > 16:
        return f"(.{'uint' if m.group(1) else 'int'} {int(m.group(2))})"
    if t == "address":
        return "(.uint 160)"
    if re.fullmatch(r"bytes\d+", t):
        return "(.uint 256)"
    return None


def core_repr(module):
    """SolidCore's checked core contract of Source.MODULE, printed as a Lean term."""
    subprocess.run(["lake", "build", f"SolidCore.Refinement.Source.{module}"], check=True,
                   stdout=subprocess.DEVNULL)
    with tempfile.NamedTemporaryFile("w", suffix=".lean", delete=False) as f:
        f.write(f"""import SolidCore.Refinement.Source.{module}
open SolidCore.Solidity
#eval match TypeCheck.CheckedInput.contract
    SolidCore.Refinement.Source.{module}.importedSourceUnit "Main" with
  | .ok c => IO.println (repr c.core).pretty
  | .error _ => IO.println "error"
""")
    out = subprocess.run(["lake", "env", "lean", f.name], check=True, capture_output=True,
                         text=True).stdout.rstrip("\n")
    Path(f.name).unlink()
    if out == "error" or not out.startswith("{"):
        print(f"{source}: no proof: SolidCore rejects the contract")
        sys.exit(3)
    return out


def deployed_storage(module):
    """The storage SolidCore's constructor of Source.MODULE leaves with the proof's fuel, as
    Abi.deployedStorage lists it (slot, word) by slot, printed as a Lean term."""
    subprocess.run(["lake", "build", "SolidCore.Refinement.Abi", f"SolidCore.Refinement.Source.{module}"],
                   check=True, stdout=subprocess.DEVNULL)
    with tempfile.NamedTemporaryFile("w", suffix=".lean", delete=False) as f:
        f.write(f"""import SolidCore.Refinement.Abi
import SolidCore.Refinement.Source.{module}
open SolidCore.Solidity SolidCore.Refinement.Abi
#eval match TypeCheck.CheckedInput.contract
    SolidCore.Refinement.Source.{module}.importedSourceUnit "Main" with
  | .ok c =>
    match deployedStorage {fuel} c with
    | some s => IO.println (" ".intercalate ("storage" :: s.map fun (kv : Nat × Nat) => s!"{{kv.1}}:{{kv.2}}"))
    | none => IO.println "error"
  | .error _ => IO.println "error"
""")
    out = subprocess.run(["lake", "env", "lean", f.name], check=True, capture_output=True,
                         text=True).stdout.split()
    Path(f.name).unlink()
    if not out or out[0] != "storage":
        print(f"{source}: no proof: SolidCore's constructor fails")
        sys.exit(3)
    entries = [tuple(int(x) for x in kv.split(":")) for kv in out[1:]]
    return "[" + ", ".join(f"({k}, {v})" for k, v in entries) + "]", [k for k, _ in entries]


def selector_block(fns):
    """The selector table of the functions fns (tuples whose first item is the name): one
    kernel_rfl check of each selector by Keccak-256 of its signature against the bytecode
    file's, the table selectorTable, and selector_eq : ABI.selectorFromSignature =
    selectorTable, which kernel_rfl's using passes to the shape checks. The signatures are
    solar's (hashes), each checked against solc's AST functionSelector."""
    hashes = main.get("hashes") or {}
    sigs = []
    for f in fns:
        n = f[0]
        sig = [g for g in hashes if g.split("(")[0] == n]
        if len(sig) != 1:
            sys.exit(f"{source}: no unique signature of {n} in solar's hashes")
        sel = hashes[sig[0]]
        if solc_selectors.get(n) != sel:
            sys.exit(f"{source}: solar's selector {sel} of {sig[0]} is not solc's {solc_selectors.get(n)}")
        sigs.append((n, sig[0]))
    word = "SolidCore.Solidity.Shared.Word"
    sfs = "SolidCore.Solidity.Source.ABI.selectorFromSignature"
    parts = ["""/-! ## The selectors

The type checker computes each external function's selector by Keccak-256 of its
signature, which costs the kernel about 400 MB a hash. Each is checked once, alone, against
the bytecode file's, and the shape checks below run on copies that read them from
`selectorTable` (`selector_eq`). -/
"""]
    for n, sig in sigs:
        cap = n[0].upper() + n[1:]
        parts.append(f"""/-- `{n}`'s selector, by Keccak-256 of its signature. -/
def sel{cap} : {word} :=
  {sfs} "{sig}"

kernel_rfl sel{cap}_eq sel{cap} Bytecode.{module}.Main.{n}Selector
""")
    table = "\n  else ".join(f'if s = "{sig}" then Bytecode.{module}.Main.{n}Selector' for n, sig in sigs)
    cases = []
    for i, (n, sig) in enumerate(sigs):
        cap = n[0].upper() + n[1:]
        cases.append(f"""  by_cases h{i} : s = "{sig}"
  · rw [ite_eq_left h{i}, h{i}]
    exact sel{cap}_eq
  rw [ite_eq_right h{i}]""")
    parts.append(f"""/-- `ABI.selectorFromSignature`, with `Main`'s signatures by table. -/
def selectorTable (s : String) : {word} :=
  {table}
  else {sfs} s

theorem selector_eq : {sfs} = selectorTable := by
  funext s
  unfold selectorTable
{chr(10).join(cases)}
""")
    return "\n".join(parts)


def shape_block(storage_lit, deployed_fn, deployed_doc):
    """shape?, its kernel check shape_eq, and shape_of and contract_ok, for a constructor that
    leaves the storage storage_lit (a Lean list), checked by the Bool deployed_fn on c."""
    return f"""/-- SolidCore's checked core of `Main`, the storage its constructor leaves and whether
it leaves {deployed_doc} and no logs, when `Main` type checks. -/
def shape? : Option (Contract × Option (List (Nat × Nat)) × Bool) :=
  match contract? with
  | .ok c => some (c.core, deployedStorage fuel c, {deployed_fn})
  | .error _ => none

-- `shape_eq : shape? = some (coreLit, some {storage_lit}, true)`: `Main` type checks, its
-- core is `coreLit` and its constructor leaves {deployed_doc} and no logs, by the kernel's
-- conversion check on the copy of `shape?` that reads the selectors from `selectorTable`
-- (`selector_eq`): one check evaluates the type checker once and hashes nothing, where a
-- `Bool` test of the core would need a decision procedure for equality of cores.
kernel_rfl shape_eq shape? (some (coreLit, some {storage_lit}, true)) using selector_eq

/-- The checked contract has the core `coreLit`, and its constructor leaves {deployed_doc}
and no logs. -/
theorem shape_of {{c : TypeCheck.CheckedContract}} (hc : contract? = .ok c) :
    c.core = coreLit ∧ deployedStorage fuel c = some {storage_lit} ∧ {deployed_fn} = true := by
  have h := shape_eq
  unfold shape? at h
  rw [hc] at h
  obtain ⟨hk, h⟩ := Prod.mk.inj (Option.some.inj h)
  obtain ⟨hs, he⟩ := Prod.mk.inj h
  exact ⟨hk, hs, he⟩

/-- `Main` type checks. -/
theorem contract_ok : ∃ c, contract? = .ok c := by
  have h := shape_eq
  unfold shape? at h
  cases hc : contract? with
  | ok c => exact ⟨c, rfl⟩
  | error _ => rw [hc] at h; simp at h
"""


def wide_parts(fns, storage=None):
    """The pieces of a symbolic proof: the printed core contract as a term, and one call_*
    theorem per function. With storage, the Lean list of the deployed storage
    and its slots from deployed_storage, every call starts from that storage."""
    lit = core_repr(module)
    term = "\n".join("  " + line for line in lit.split("\n"))
    ns = f"SolidCore.Refinement.Corpus.{module}"
    header = f"-- Generated by scripts/refinement/gen.sh from {source}. Do not edit.\n"
    fn_list = ",\n    ".join(
        f"⟨Bytecode.{module}.Main.{n}Selector, [{', '.join(ps)}]⟩" for n, ps, _ in fns
    )
    selectors = ", ".join(f"Bytecode.{module}.Main.{n}Selector" for n, _, _ in fns)
    rules = f"code, Bytecode.{module}.Main.runtimeNat, Bytecode.{module}.Main.runtimeSize, {selectors}"
    theorems = []
    for n, ps, writes in fns:
        k = len(ps)
        ws = [f"w{i + 1}" for i in range(k)]
        if writes:
            # A function that may write storage: the bytecode's state is checked slot by slot.
            target = f"""  all_goals
    refine run_of_postS code _ [{', '.join(ws)}] _ (by simp [Source.observe, State.logEntries, hev])
      (fun hX slot => by simp_all [Source.observe, slotValue, callOf]) ?_
  all_goals wide_tgt_s [{rules}]
"""
        else:
            target = f"""  all_goals
    refine run_of_post code _ [{', '.join(ws)}] _ (by simp [Source.observe, State.logEntries, hev])
      (fun slot => by
        simp [Source.observe, State.loadSlot, StorageMap.lookup?, getElem?_of_isEmpty hs,
          slotValue, callOf]) ?_
  all_goals wide_tgt [{rules}]
"""
        pattern = "_"
        for w in reversed(ws):
            pattern = f"_ | ⟨{w}, {pattern}⟩"
        if storage is not None:
            # A call from the deployed storage: SLOAD reads it and the bytecode's state is checked
            # slot by slot, for every function.
            lit, keys = storage
            conds = "".join(f"k ≠ {key} → " for key in keys)
            names = " ".join(f"h{i}" for i in range(len(keys)))
            theorems.append(f"""set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
/-- SolidCore and solar's bytecode agree on every call of `{n}` on any argument words, from the
deployed storage. -/
theorem call_{n} {{c : TypeCheck.CheckedContract}} (hcore : c.core = coreLit) {{d : Source.State}}
    (hd : DeployedAt fuel c d {lit}) (ws : List U256) (hl : ws.length = {k}) :
    ∃ obs, Source.run fuel c (callAt Bytecode.{module}.Main.{n}Selector ws {lit}) = some obs ∧
      Target.run code (callAt Bytecode.{module}.Main.{n}Selector ws {lit}) = some obs := by
  rcases ws with {pattern} <;> simp at hl
  rw [run_eq_at hd]
  have hev := hd.events
  have hnone : ∀ k, {conds}d.storage[k]? = none := fun k {names} =>
    hd.getElem?_eq_none fun v hv => by simp at hv; omega
  simp only [hcore, List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]
  wide_symex [coreLit, fuel, ctxOf, hcore, {selectors}, get?_insert]
  all_goals
    refine run_of_postS_at code _ [{', '.join(ws)}] _ _ (by simp [Source.observe, State.logEntries, hev])
      (fun hX slot => by simp_all [Source.observe, callAt]) ?_
  all_goals wide_tgt_at [{rules}]
""")
            continue
        theorems.append(f"""set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
/-- SolidCore and solar's bytecode agree on every call of `{n}` on any argument words. -/
theorem call_{n} {{c : TypeCheck.CheckedContract}} (hcore : c.core = coreLit) {{d : Source.State}}
    (hd : Deployed fuel c d) (ws : List U256) (hl : ws.length = {k}) :
    ∃ obs, Source.run fuel c (callOf Bytecode.{module}.Main.{n}Selector ws) = some obs ∧
      Target.run code (callOf Bytecode.{module}.Main.{n}Selector ws) = some obs := by
  rcases ws with {pattern} <;> simp at hl
  rw [run_eq hd]
  have hs := hd.storage
  have hev := hd.events
  simp only [hcore, List.map_cons, List.map_nil]
  wide_symex [coreLit, fuel, ctxOf, hcore, {selectors}]
{target}""")
    return term, theorems


def gen_wide(fns):
    """Write MODULE.lean, the symbolic refinement of a contract with wide parameters."""
    term, theorems = wide_parts(fns)
    ns = f"SolidCore.Refinement.Corpus.{module}"
    header = f"-- Generated by scripts/refinement/gen.sh from {source}. Do not edit.\n"
    fn_list = ",\n    ".join(
        f"⟨Bytecode.{module}.Main.{n}Selector, [{', '.join(ps)}]⟩" for n, ps, _ in fns
    )
    cases = " | ".join(["rfl"] * len(fns))
    dispatch = "\n".join(f"  · exact call_{n} hcore hd ws hl" for n, _, _ in fns)
    extra_import = "import SolidCore.Refinement.KernelCopies\nimport SolidCore.Refinement.KernelRfl\n"
    shape_doc = """The kernel checks `shape_eq` (`kernel_rfl`, `SolidCore.Refinement.KernelRfl`): that
SolidCore's checked contract has the core `coreLit`, the generator's print of it, and that
its constructor leaves no storage and no logs, by one conversion check that evaluates copies
of the type checker and the interpreter, which read each function's selector from
`selectorTable` (`selector_eq`, each selector checked by Keccak-256 on its own)."""
    if kernel_shape:
        shape_doc += """
`wide_tgt` decides branches by evaluation and `bv_omega`."""
    else:
        shape_doc += """
`wide_tgt` decides branches by evaluation and `bv_omega`, and by `bv_decide` (which
trusts Lean's compiler) only where those fail."""
    selectors = selector_block(fns)
    shape = shape_block("[]", "deployedEmpty fuel c", "no storage")
    (out / f"{module}.lean").write_text(f"""{header}
import SolidCore.Refinement.Wide.Refines
import SolidCore.Refinement.Bytecode.{module}
import SolidCore.Refinement.Source.{module}
{extra_import}
/-!
# {name}: solar's bytecode refines SolidCore's `Main` on wide arguments

`refines_full` proves `Refines fuel contract code (fullScope fns s)` for `Main` in
`{source}`, where `code` is solar's runtime bytecode at the pinned commit and `s` the
storage SolidCore's constructor leaves (none): every call of every function on any
argument words below `2 ^ 256`, with no value. Each `call_*` theorem runs one function
symbolically in both semantics (`SolidCore.Refinement.Wide`): SolidCore's interpreter by
`wide_symex`, solar's bytecode on EthLib by `wide_tgt`, path by path.

{shape_doc}
-/

namespace {ns}

open EthLib.Base SolidCore.Refinement SolidCore.Refinement.Abi SolidCore.Refinement.Wide
open SolidCore.Refinement.Evm.Wide SolidCore.Solidity SolidCore.Solidity.Source

/-- The interpreter fuel the refinement uses. -/
def fuel : Nat := {fuel}

/-- solar's runtime bytecode of `Main`, from the generated file. -/
def code : ByteArray :=
  EthLib.Execution.Evm.Logic.NatCode.ofNat Bytecode.{module}.Main.runtimeNat
    Bytecode.{module}.Main.runtimeSize

/-- SolidCore's checked `Main`. -/
def contract? : Except TypeCheck.TypeError TypeCheck.CheckedContract :=
  TypeCheck.CheckedInput.contract Source.{module}.importedSourceUnit "Main"

/-- The functions of `Main` and their parameters. A wide parameter counts as the
`Param` of its width; `fullScope` only counts them. -/
def fns : List Fn :=
  [{fn_list}]

/-- SolidCore's core contract of `Main`, as the generator printed it. -/
def coreLit : Contract :=
{term}

{selectors}
{shape}
{chr(10).join(theorems)}
/-- solar's runtime bytecode of `Main` refines SolidCore's `Main` on every call of every
function with any argument words below `2 ^ 256`, from the deployed storage. -/
theorem refines_full : ∃ c s, contract? = .ok c ∧ deployedStorage fuel c = some s ∧
    Refines fuel c code (fullScope fns s) := by
  obtain ⟨c, hc⟩ := contract_ok
  obtain ⟨hcore, hdep, hemp⟩ := shape_of hc
  obtain ⟨d, hd⟩ := deployed_of hemp
  refine ⟨c, [], hc, hdep, refines_of_calls fun fn hfn ws hl => ?_⟩
  simp only [fns, List.mem_cons, List.not_mem_nil, or_false] at hfn
  rcases hfn with {cases}
{dispatch}

end {ns}
""")
    print(f"{source} -> {out}/{module}.lean (wide, {len(fns)} function(s), symbolic)")



ROUTES = Path("scripts/refinement/routes")


def select_route():
    """The proof route of a contract whose parameters are all small: "symbolic" (both
    semantics run on free argument words, as for a wide contract) or "enum" (every clean
    call by native_decide, every dirty one by dirty_symex). A line
    "// refinement: route=symbolic" or "route=enum" in the source picks it; otherwise
    scripts/refinement/routes, which lists the contracts whose symbolic proof builds in
    reasonable time, does; otherwise "enum", which always applies."""
    m = re.search(r"//\s*refinement:.*\broute=(symbolic|enum)\b", Path(source).read_text())
    if m:
        return m.group(1)
    if ROUTES.exists():
        for line in ROUTES.read_text().splitlines():
            words = line.split("#", 1)[0].split()
            if len(words) == 2 and words[0] == name and words[1] in ("symbolic", "enum"):
                return words[1]
    return "enum"


def gen_small_symbolic():
    """Write MODULE.lean, the symbolic refinement of a contract whose parameters are all
    small, next to MODULE/Defs.lean and MODULE/Dirty.lean, which the sequence proof uses.
    When the constructor leaves storage, every call starts from it: the call_* theorems are
    stated on Evm.Wide.callAt of the deployed storage and proved by wide_tgt_at."""
    mut = {i["name"]: i.get("stateMutability") for i in abi if i.get("type") == "function"}
    wfns = [(n, ps, mut[n] not in ("pure", "view")) for n, ps in fns]
    # A constructor that leaves storage: every call starts from it (Wide.refines_of_calls_at).
    lit, keys = deployed_storage(module)
    term, theorems = wide_parts(wfns, (lit, keys) if keys else None)
    if keys:
        leaves = f"the storage `{lit}`"
        leaves_note = f"(`{lit}`)"
        tgt = "wide_tgt_at"
        tgt_doc = """ `wide_tgt_at` decides branches by evaluation and
`bv_omega`, and compares the words left by evaluating them on every value of a small argument
word in the kernel (`word_decide`)."""
        shape = shape_block(lit, f"deployedAt fuel c {lit}", f"the storage `{lit}`")
        deployed_of = "obtain ⟨d, hd⟩ := deployedAt_of hemp"
        refines_of = f"refine ⟨c, {lit}, hc, hdep, refines_of_calls_at fun fn hfn ws hl => ?_⟩"
    else:
        leaves = "no storage"
        leaves_note = "(none)"
        tgt = "wide_tgt"
        tgt_doc = """ `wide_tgt` decides branches by evaluation and `bv_omega`."""
        shape = shape_block("[]", "deployedEmpty fuel c", "no storage")
        deployed_of = "obtain ⟨d, hd⟩ := deployed_of hemp"
        refines_of = "refine ⟨c, [], hc, hdep, refines_of_calls fun fn hfn ws hl => ?_⟩"
    cases = " | ".join(["rfl"] * len(fns))
    dispatch = "\n".join(f"  · exact call_{n} hcore hd ws hl" for n, _, _ in wfns)
    kernel_import = "import SolidCore.Refinement.KernelCopies\nimport SolidCore.Refinement.KernelRfl\n"
    selectors = selector_block(wfns)
    core_doc = f"""The kernel checks `shape_eq` (`kernel_rfl`, `SolidCore.Refinement.KernelRfl`): that
SolidCore's checked contract has the core `coreLit`, the generator's print of it, and that
its constructor leaves {leaves} and no logs, by one conversion check that evaluates copies
of the type checker and the interpreter, which read each function's selector from
`selectorTable` (`selector_eq`, each selector checked by Keccak-256 on its own)."""
    if kernel_shape:
        core_doc += tgt_doc
        shape_proof = "kernel_rfl shapeOk_eq_true shapeOk true using selector_eq"
    else:
        core_doc += f"""
`{tgt}` decides branches by evaluation and `bv_omega`, and by `bv_decide` (which
trusts Lean's compiler) only where those fail."""
        shape_proof = "theorem shapeOk_eq_true : shapeOk = true := by native_decide"
    (out / f"{module}.lean").write_text(f"""{header}
import SolidCore.Refinement.Wide.Refines
import SolidCore.Refinement.Wide.Clean
import {ns}.Defs
import {ns}.Dirty
{kernel_import}
/-!
# {name}: solar's bytecode refines SolidCore's `Main`, symbolically

`refines_full` proves `Refines fuel contract code (fullScope fns s)` for `Main` in
`{source}`, where `code` is solar's runtime bytecode at the pinned commit and `s` the
storage SolidCore's constructor leaves {leaves_note}: every call of every function on any
argument words below `2 ^ 256`, clean or dirty, with no value. Each `call_*` theorem runs
one function symbolically in both semantics (`SolidCore.Refinement.Wide`): SolidCore's
interpreter by `wide_symex`, solar's bytecode on EthLib by `{tgt}`, path by path, so no
call is run by `native_decide`. `refines`, on the clean calls of `scope s`, follows.

{core_doc}
`shapeOk` and `Dirty.lean` serve the sequence proof (`Seq.lean`), not these theorems.
-/

namespace {ns}

open EthLib.Base SolidCore.Refinement SolidCore.Refinement.Abi SolidCore.Refinement.Wide
open SolidCore.Refinement.Evm.Wide SolidCore.Solidity SolidCore.Solidity.Source

/-- SolidCore's core contract of `Main`, as the generator printed it. -/
def coreLit : Contract :=
{term}

{selectors}
{shape}
{chr(10).join(theorems)}
/-- solar's runtime bytecode of `Main` refines SolidCore's `Main` on every call of every
function with any argument words below `2 ^ 256`, from the deployed storage. -/
theorem refines_full : ∃ c s, contract? = .ok c ∧ deployedStorage fuel c = some s ∧
    Refines fuel c code (fullScope fns s) := by
  obtain ⟨c, hc⟩ := contract_ok
  obtain ⟨hcore, hdep, hemp⟩ := shape_of hc
  {deployed_of}
  {refines_of}
  simp only [fns, List.mem_cons, List.not_mem_nil, or_false] at hfn
  rcases hfn with {cases}
{dispatch}

/-- solar's runtime bytecode of `Main` refines SolidCore's `Main` on every call of
the scope: every clean call. -/
theorem refines : ∃ c s, contract? = .ok c ∧ deployedStorage fuel c = some s ∧
    Refines fuel c code (· ∈ scope s) := by
  obtain ⟨c, s, hc, hs, h⟩ := refines_full
  exact ⟨c, s, hc, hs, refines_of_full (by decide) h⟩

/-- Whether every function of `fns` has the shape `Dirty.run_dirty` covers, in
SolidCore's checked `Main`. -/
def shapeOk : Bool :=
  match contract? with
  | .ok c => fns.all (Dirty.fnShapeOk c)
  | .error _ => false

{shape_proof}

end {ns}
""")
    print(f"{source} -> {out}/{module}.lean ({total} calls, symbolic)")


def dyn_param(p):
    """The Dyn.DParam of a parameter and its number of encodings within the bounds, or
    (None, None). A dynamic parameter is bytes, an array of a small type or a struct of
    small types; a small one is a word."""
    t = p["type"]
    if t == "bytes":
        n = DYN_BYTES
        return f"(.bytes {n})", sum(256 ** k for k in range(n + 1))
    if t.endswith("[]"):
        ep, count = param({**p, "type": t[:-2], "internalType": p.get("internalType", "")[:-2]})
        if ep is None:
            return None, None
        n = DYN_ARRAY
        return f"(.array {ep} {n})", sum(count ** k for k in range(n + 1))
    if t == "tuple":
        comps = [param(c) for c in p["components"]]
        if not comps or any(c[0] is None for c in comps):
            return None, None
        return f"(.struct [{', '.join(c[0] for c in comps)}])", math.prod(c[1] for c in comps)
    w, count = param(p)
    if w is None:
        return None, None
    return f"(.word {w})", count


DYN_BYTES = 2
DYN_ARRAY = 2
m = re.search(r"//\s*refinement:.*\bbytes=(\d+)", Path(source).read_text())
if m:
    DYN_BYTES = int(m.group(1))
m = re.search(r"//\s*refinement:.*\barray=(\d+)", Path(source).read_text())
if m:
    DYN_ARRAY = int(m.group(1))


def gen_dyn(items):
    """Write the refinement of a contract with dynamic or struct parameters: the canonical
    encodings within the bounds by evaluation, malformed call data symbolically."""
    fns = []
    total = 0
    for item in items:
        ps = [dyn_param(p) for p in item["inputs"]]
        if any(p[0] is None for p in ps):
            bad = ", ".join(p["type"] for p in item["inputs"])
            print(f"{source}: no proof: {item['name']}({bad}) has a parameter outside the scope")
            sys.exit(3)
        fns.append((item["name"], [p[0] for p in ps]))
        total += math.prod(p[1] for p in ps)
    if total > MAX_CALLS:
        print(f"{source}: no proof: {total} encodings is outside the finite scope")
        sys.exit(3)
    parts = max(1, math.ceil(total / CALLS_PER_PART))
    ns = f"SolidCore.Refinement.Corpus.{module}"
    out = Path("SolidCore/Refinement/Corpus")
    (out / module).mkdir(parents=True, exist_ok=True)
    header = f"-- Generated by scripts/refinement/gen.sh from {source}. Do not edit.\n"
    fn_list = ",\n    ".join(
        f"⟨Bytecode.{module}.Main.{n}Selector, [{', '.join(ps)}]⟩" for n, ps in fns
    )
    (out / module / "Defs.lean").write_text(f"""{header}
import SolidCore.Refinement.Dyn.Abi
import SolidCore.Refinement.Check
import SolidCore.Refinement.Bytecode.{module}
import SolidCore.Refinement.Source.{module}

/-!
# The scope of {name}'s refinement

{total} calls: every function of `Main` in `{source}` on the canonical ABI encoding of
every argument tuple within the bounds (`Dyn.encodings`), with no value, from the storage
SolidCore's constructor leaves. The check runs in {parts} part(s), each in its own module.
-/

namespace {ns}

open SolidCore.Refinement SolidCore.Refinement.Abi SolidCore.Refinement.Dyn SolidCore.Solidity

/-- The interpreter fuel the refinement uses. -/
def fuel : Nat := {fuel}

/-- solar's runtime bytecode of `Main`, from the generated file. -/
def code : ByteArray :=
  EthLib.Execution.Evm.Logic.NatCode.ofNat Bytecode.{module}.Main.runtimeNat
    Bytecode.{module}.Main.runtimeSize

/-- SolidCore's checked `Main`. -/
def contract? : Except TypeCheck.TypeError TypeCheck.CheckedContract :=
  TypeCheck.CheckedInput.contract Source.{module}.importedSourceUnit "Main"

/-- The functions of `Main` and their parameters, with the bounds of their encodings. -/
def fns : List DFn :=
  [{fn_list}]

/-- The number of parts the check runs in. -/
def parts : Nat := {parts}

/-- The calls the evaluation covers, from the deployed storage `s`. -/
def scope (s : List (Nat × Nat)) : List Call := encodings fns [s]

/-- Whether both semantics agree on every `parts`-th call of the scope, from the `i`-th. -/
def partOk (i : Nat) : Bool :=
  match contract? with
  | .ok c =>
    match deployedStorage fuel c with
    | some s => checkPart (agree fuel c code) (scope s).toArray parts i
    | none => false
  | .error _ => false

end {ns}
""")
    for i in range(parts):
        (out / module / f"Part{i}.lean").write_text(f"""{header}
import {ns}.Defs

namespace {ns}

theorem part{i} : partOk {i} = true := by native_decide

end {ns}
""")
    rules = ", ".join(
        [f"Bytecode.{module}.Main.runtimeNat", f"Bytecode.{module}.Main.runtimeSize"]
        + [f"Bytecode.{module}.Main.{n}Selector" for n, _ in fns]
    )
    fn_cases = "\n".join(
        f"  · exact malformed_of_frame code Bytecode.{module}.Main.{n}Selector [{', '.join(ps)}]\n"
        f"      (by dyn_symex [code, {rules}])"
        for n, ps in fns
    )
    pattern = " | ".join(["rfl"] * len(fns))
    (out / module / "Malformed.lean").write_text(f"""{header}
import SolidCore.Refinement.Dyn.Refines
import {ns}.Defs

/-!
# {name}: EthLib rejects malformed call data

For every function of `Main` in `{source}`, every call whose call data after the
selector is malformed (`Dyn.Malformed`: shorter than the heads, or a dynamic argument
pointing past the end), of any length below `2 ^ 32` and with any bytes, reverts with
empty output in EthLib, from any storage. Each case is one `dyn_symex` run over solar's
bytecode, symbolic in the call data's size and bytes.
-/

namespace {ns}

open SolidCore.Refinement SolidCore.Refinement.Abi SolidCore.Refinement.Dyn

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8192 in
/-- EthLib rejects every malformed call of every function of `Main`. -/
theorem target_malformed : TargetMalformed code fns := by
  intro fn hfn
  simp only [fns, List.mem_cons, List.not_mem_nil, or_false] at hfn
  rcases hfn with {pattern}
{fn_cases}

end {ns}
""")
    imports = "\n".join(f"import {ns}.Part{i}" for i in range(parts))
    imports += f"\nimport {ns}.Malformed"
    cases = "\n".join(f"  | {i}, _ => part{i}" for i in range(parts))
    (out / f"{module}.lean").write_text(f"""{header}
{imports}

/-!
# {name}: solar's bytecode refines SolidCore's `Main` on dynamic parameters

`refines` proves `Refines fuel contract code (· ∈ scope s)` for `Main` in `{source}`,
where `code` is solar's runtime bytecode at the pinned commit and `s` the storage
SolidCore's constructor leaves. The scope is every call of every function on the
canonical encoding of an argument tuple within the bounds, {total} calls, each run in both
semantics by `native_decide` (which trusts Lean's compiler).

`refines_full` extends it to `Dyn.dynScope`: also every call on malformed call data,
which both sides reject with empty output, by `Dyn.run_malformed` for SolidCore (once
`native_decide` checks each function's shape) and by `target_malformed` for EthLib.
-/

namespace {ns}

open SolidCore.Refinement SolidCore.Refinement.Abi SolidCore.Refinement.Dyn

theorem parts_ok : ∀ i < parts, partOk i = true := fun i hi =>
  match i, hi with
{cases}
  | n + {parts}, h => absurd h (by simp only [parts]; omega)

/-- solar's runtime bytecode of `Main` refines SolidCore's `Main` on every canonical
encoding within the bounds. -/
theorem refines : ∃ c s, contract? = .ok c ∧ deployedStorage fuel c = some s ∧
    Refines fuel c code (· ∈ scope s) := by
  have h0 := parts_ok 0 (by decide)
  match hc : contract?, h0 with
  | .ok c, h0 =>
    match hs : deployedStorage fuel c with
    | some s =>
      refine ⟨c, s, rfl, hs, refines_of_all (all_of_parts (parts := parts) (by decide) fun i hi => ?_)⟩
      have := parts_ok i hi
      simpa only [partOk, hc, hs] using this
    | none => simp [partOk, hc, hs] at h0
  | .error _, h0 => simp [partOk, hc] at h0

/-- Whether every function of `fns` has the shape `Dyn.run_malformed` covers, in
SolidCore's checked `Main`. -/
def shapeOk : Bool :=
  match contract? with
  | .ok c => fns.all (dfnShapeOk c)
  | .error _ => false

theorem shapeOk_eq_true : shapeOk = true := by native_decide

/-- solar's runtime bytecode of `Main` refines SolidCore's `Main` on every call of every
function on a canonical encoding within the bounds or on malformed call data shorter than
`2 ^ 32`, from the deployed storage. -/
theorem refines_full : ∃ c s, contract? = .ok c ∧ deployedStorage fuel c = some s ∧
    Refines fuel c code (dynScope fns s) := by
  obtain ⟨c, s, hc, hs, h⟩ := refines
  have hsh := shapeOk_eq_true
  simp only [shapeOk, hc] at hsh
  exact ⟨c, s, hc, hs, refines_dyn hs h hsh target_malformed⟩

end {ns}
""")
    print(f"{source} -> {out}/{module}.lean (dynamic, {total} encodings, {parts} part(s), malformed symbolic)")


dyn_items = sorted((i for i in abi if i.get("type") == "function"), key=lambda i: i["name"])
if any(p["type"] in ("bytes", "tuple") or p["type"].endswith("[]")
       for i in dyn_items for p in i["inputs"]):
    gen_dyn(dyn_items)
    sys.exit(0)

wide = False
for item in sorted((i for i in abi if i.get("type") == "function"), key=lambda i: i["name"]):
    if any(param(p)[0] is None and wide_param(p) is not None for p in item["inputs"]):
        wide = True
fns_wide = []
if wide:
    for item in sorted((i for i in abi if i.get("type") == "function"), key=lambda i: i["name"]):
        ps = [param(p)[0] or wide_param(p) for p in item["inputs"]]
        if any(p is None for p in ps):
            bad = ", ".join(p["type"] for p in item["inputs"])
            print(f"{source}: no proof: {item['name']}({bad}) has a parameter outside the scope")
            sys.exit(3)
        writes = item.get("stateMutability") not in ("pure", "view")
        fns_wide.append((item["name"], ps, writes))
    out = Path("SolidCore/Refinement/Corpus")
    out.mkdir(parents=True, exist_ok=True)
    gen_wide(fns_wide)
    sys.exit(0)

fns = []
total = 0
for item in sorted((i for i in abi if i.get("type") == "function"), key=lambda i: i["name"]):
    params = [param(p) for p in item["inputs"]]
    if any(p[0] is None for p in params):
        bad = ", ".join(p["type"] for p in item["inputs"])
        print(f"{source}: no proof: {item['name']}({bad}) has a parameter outside the finite scope")
        sys.exit(3)
    fns.append((item["name"], [p[0] for p in params]))
    total += math.prod(p[1] for p in params)
if not fns or total > MAX_CALLS:
    print(f"{source}: no proof: {total} calls is outside the finite scope")
    sys.exit(3)

parts = max(1, math.ceil(total / CALLS_PER_PART))
route = select_route()
ns = f"SolidCore.Refinement.Corpus.{module}"
out = Path("SolidCore/Refinement/Corpus")
(out / module).mkdir(parents=True, exist_ok=True)
header = f"-- Generated by scripts/refinement/gen.sh from {source}. Do not edit.\n"
fn_list = ",\n    ".join(
    f"⟨Bytecode.{module}.Main.{n}Selector, [{', '.join(ps)}]⟩" for n, ps in fns
)

(out / module / "Defs.lean").write_text(f"""{header}
import SolidCore.Refinement.Abi
import SolidCore.Refinement.Bytecode.{module}
import SolidCore.Refinement.Source.{module}

/-!
# The scope of {name}'s refinement

{total} calls: every function of `Main` in `{source}` on every list of clean
argument words, with no value, from the storage SolidCore's constructor leaves.
The check runs in {parts} part(s), each in its own module.
-/

namespace {ns}

open SolidCore.Refinement SolidCore.Refinement.Abi SolidCore.Solidity

/-- The interpreter fuel the refinement uses. -/
def fuel : Nat := {fuel}

/-- solar's runtime bytecode of `Main`, from the generated file. -/
def code : ByteArray :=
  EthLib.Execution.Evm.Logic.NatCode.ofNat Bytecode.{module}.Main.runtimeNat
    Bytecode.{module}.Main.runtimeSize

/-- SolidCore's checked `Main`. -/
def contract? : Except TypeCheck.TypeError TypeCheck.CheckedContract :=
  TypeCheck.CheckedInput.contract Source.{module}.importedSourceUnit "Main"

/-- The functions of `Main` and their parameters. -/
def fns : List Fn :=
  [{fn_list}]

/-- The number of parts the check runs in. -/
def parts : Nat := {parts}

/-- The calls the theorem covers, from the deployed storage `s`. -/
def scope (s : List (Nat × Nat)) : List Call := calls fns [s]

/-- Whether both semantics agree on every `parts`-th call of the scope, from the `i`-th. -/
def partOk (i : Nat) : Bool :=
  match contract? with
  | .ok c =>
    match deployedStorage fuel c with
    | some s => checkPart (agree fuel c code) (scope s).toArray parts i
    | none => false
  | .error _ => false

end {ns}
""")

if route == "enum":
    for i in range(parts):
        (out / module / f"Part{i}.lean").write_text(f"""{header}
import {ns}.Defs

namespace {ns}

theorem part{i} : partOk {i} = true := by native_decide

end {ns}
""")

rules = ", ".join(
    [f"Bytecode.{module}.Main.runtimeNat", f"Bytecode.{module}.Main.runtimeSize"]
    + [f"Bytecode.{module}.Main.{n}Selector" for n, _ in fns]
)
fn_cases = "\n".join(
    f"  · exact dirty_of_frame code Bytecode.{module}.Main.{n}Selector [{', '.join(ps)}]\n"
    f"      (by dirty_symex [code, {rules}])"
    for n, ps in fns
)
pattern = " | ".join(["rfl"] * len(fns))
(out / module / "Dirty.lean").write_text(f"""{header}
import SolidCore.Refinement.Evm.Symex
import SolidCore.Refinement.Dirty.Source
import {ns}.Defs

/-!
# {name}: EthLib rejects every dirty argument word

For every function of `Main` in `{source}`, every call whose argument words are
below `2 ^ 256` but not all clean reverts with empty output in EthLib, from any
storage. Each case is one `dirty_symex` run over solar's bytecode, symbolic in
the argument words; `bv_omega` decides its branch conditions, a kernel-checked
proof (`symex_bv` falls back to `bv_decide` only where it fails).
-/

namespace {ns}

open SolidCore.Refinement SolidCore.Refinement.Abi SolidCore.Refinement.Evm.Symex

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8192 in
/-- EthLib rejects every dirty call of every function of `Main`. -/
theorem target_dirty : Dirty.TargetDirty code fns := by
  intro fn hfn
  simp only [fns, List.mem_cons, List.not_mem_nil, or_false] at hfn
  rcases hfn with {pattern}
{fn_cases}

end {ns}
""")

if route == "enum":
    imports = "\n".join(f"import {ns}.Part{i}" for i in range(parts))
    imports += f"\nimport {ns}.Dirty"
    cases = "\n".join(f"  | {i}, _ => part{i}" for i in range(parts))
    (out / f"{module}.lean").write_text(f"""{header}
{imports}

/-!
# {name}: solar's bytecode refines SolidCore's `Main`

`refines` proves `Refines fuel contract code (· ∈ scope s)` for `Main` in
`{source}`, where `code` is solar's runtime bytecode at the pinned commit and `s`
the storage SolidCore's constructor leaves. The scope is every call of every
function on clean argument words with no value, {total} calls, each run in
both semantics by `native_decide` (which trusts Lean's compiler).

`refines_full` extends it to every argument word below `2 ^ 256`: a dirty word
makes both sides revert with empty output and keep the storage, by
`Dirty.run_dirty` for SolidCore (once `native_decide` checks each function's
shape) and by `target_dirty` for EthLib.
-/

namespace {ns}

open SolidCore.Refinement SolidCore.Refinement.Abi

theorem parts_ok : ∀ i < parts, partOk i = true := fun i hi =>
  match i, hi with
{cases}
  | n + {parts}, h => absurd h (by simp only [parts]; omega)

/-- solar's runtime bytecode of `Main` refines SolidCore's `Main` on every call of
the scope: every clean call. -/
theorem refines : ∃ c s, contract? = .ok c ∧ deployedStorage fuel c = some s ∧
    Refines fuel c code (· ∈ scope s) := by
  have h0 := parts_ok 0 (by decide)
  match hc : contract?, h0 with
  | .ok c, h0 =>
    match hs : deployedStorage fuel c with
    | some s =>
      refine ⟨c, s, rfl, hs, refines_of_all (all_of_parts (parts := parts) (by decide) fun i hi => ?_)⟩
      have := parts_ok i hi
      simpa only [partOk, hc, hs] using this
    | none => simp [partOk, hc, hs] at h0
  | .error _, h0 => simp [partOk, hc] at h0

/-- Whether every function of `fns` has the shape `Dirty.run_dirty` covers, in
SolidCore's checked `Main`. -/
def shapeOk : Bool :=
  match contract? with
  | .ok c => fns.all (Dirty.fnShapeOk c)
  | .error _ => false

theorem shapeOk_eq_true : shapeOk = true := by native_decide

/-- solar's runtime bytecode of `Main` refines SolidCore's `Main` on every call of every
function with any argument words below `2 ^ 256`, clean or dirty, from the deployed
storage: the clean calls by `refines`, the dirty ones by `Dirty.run_dirty` on the
SolidCore side and `target_dirty` on the EthLib side. -/
theorem refines_full : ∃ c s, contract? = .ok c ∧ deployedStorage fuel c = some s ∧
    Refines fuel c code (fullScope fns s) := by
  obtain ⟨c, s, hc, hs, h⟩ := refines
  have hsh := shapeOk_eq_true
  simp only [shapeOk, hc] at hsh
  exact ⟨c, s, hc, hs, Dirty.refines_full hs h hsh target_dirty⟩

end {ns}
""")
    print(f"{source} -> {out}/{module}.lean ({total} calls, {parts} part(s))")
else:
    gen_small_symbolic()




# Sequences of calls. Everything below only adds files: MODULE/SeqStates.lean,
# MODULE/SeqDefs.lean, MODULE/SeqPartI.lean and MODULE/Seq.lean, and the
# aggregate SolidCore/Refinement/Seq/Corpus.lean.
#
# The certificate is the set of storages clean calls reach from the deployed
# one, by level. A contract whose functions are all pure or view cannot write
# storage, so its certificate is the deployed storage alone, closed. Otherwise
# SolidCore.Refinement.Seq.explore computes it with SolidCore, run here through
# lake: it stops at the closure (closed: every sequence of any length) or before
# the levels would hold more than SEQ_MAX_STATES storages or need more than
# SEQ_BUDGET calls to check (open: every sequence of at most as many calls as
# there are levels). Lean re-checks the certificate on both semantics, so the
# exploration is not trusted. A failed exploration skips the sequence proof.
import os
import subprocess
import tempfile

SEQ_MAX_STATES = 1 << 12
SEQ_BUDGET = 1 << 17
SEQ_ROUNDS = 64
seq_pure = all(i.get("stateMutability") in ("pure", "view") for i in abi if i.get("type") == "function")


def seq_plan():
    if seq_pure:
        return True, total, [], []
    lake = os.environ.get("LAKE", "lake")
    build = subprocess.run([lake, "build", f"{ns}.Defs", "SolidCore.Refinement.Seq.Explore"],
                           capture_output=True, text=True)
    if build.returncode != 0:
        raise RuntimeError(build.stdout[-2000:] + build.stderr[-2000:])
    probe = f"""import SolidCore.Refinement.Seq.Explore
import {ns}.Defs
open SolidCore.Refinement SolidCore.Refinement.Abi {ns}
#eval show IO Unit from do
  match contract? with
  | .ok c =>
    match deployedStorage fuel c with
    | some s => IO.println (Seq.explore fuel c fns s {SEQ_MAX_STATES} {SEQ_BUDGET} {SEQ_ROUNDS}).render
    | none => IO.println "error"
  | .error _ => IO.println "error"
"""
    with tempfile.TemporaryDirectory() as d:
        path = Path(d) / "Probe.lean"
        path.write_text(probe)
        res = subprocess.run([lake, "env", "lean", str(path)], capture_output=True, text=True)
    lines = res.stdout.splitlines()
    starts = [i for i, l in enumerate(lines) if l in ("closed", "open")]
    if res.returncode != 0 or not starts:
        raise RuntimeError(res.stdout[-2000:] + res.stderr[-2000:])
    lines = lines[starts[0]:]
    closed = lines[0] == "closed"
    per = int(lines[1])
    keys = [int(k) for k in lines[2].split()]
    levels = []
    for line in lines[3:]:
        if not line.startswith("L "):
            break
        level = []
        for st in line[2:].split(";"):
            level.append([tuple(int(x) for x in kv.split(":")) for kv in st.split(",") if kv])
        levels.append(level)
    return closed, per, keys, levels


try:
    seq_closed, seq_per, seq_keys, seq_levels = seq_plan()
except RuntimeError as e:
    print(f"{source}: no sequence proof: exploration failed\n{e}", file=sys.stderr)
    seq_closed = None

if seq_closed is not None:
    seq_states = 1 + sum(len(l) for l in seq_levels)
    seq_calls = seq_per * seq_states
    seq_depth = 1 + len(seq_levels)
    seq_parts = max(1, math.ceil(seq_calls / CALLS_PER_PART))

    def lean_state(st):
        return "[" + ", ".join(f"({k}, {v})" for k, v in st) + "]"

    if seq_levels:
        level_txt = ",\n  ".join(
            "[" + ",\n    ".join(lean_state(st) for st in level) + "]" for level in seq_levels
        )
        levels_lit = f"[\n  {level_txt}]"
    else:
        levels_lit = "[]"
    keys_lit = "[" + ", ".join(str(k) for k in seq_keys) + "]"
    if seq_closed:
        how = ("every function is pure or view, so the deployed storage alone is closed"
               if seq_pure else "`Seq.explore` found the closure")
        variant = (f"closed: {seq_states} storage(s) in {seq_depth} level(s); {how}. The\n"
                   "theorem covers every sequence of calls of any length")
    else:
        variant = (f"open: the closure did not fit {SEQ_MAX_STATES} storages and {SEQ_BUDGET} calls,\n"
                   f"so the certificate keeps the first {seq_depth} level(s), {seq_states} storage(s). The\n"
                   f"theorem covers every sequence of at most {seq_depth} calls")

    (out / module / "SeqStates.lean").write_text(f"""{header}
/-!
# The storages {name}'s clean calls reach

The certificate of the sequence refinement of `Main` in `{source}`, as
`SolidCore.Refinement.Seq.explore` found it: the slots any reached storage holds
(`seqKeys`) and the storages of every level after the deployed one (`seqLevels`),
each as its nonzero or constructor-written slots, sorted. Nothing here is
trusted: `SeqDefs.lean` checks it against both semantics.
-/

namespace {ns}

/-- The slots a reached storage holds a word for. -/
def seqKeys : List Nat := {keys_lit}

/-- The reached storages, by level, from level 1. -/
def seqLevels : List (List (List (Nat × Nat))) := {levels_lit}

end {ns}
""")

    (out / module / "SeqDefs.lean").write_text(f"""{header}
import SolidCore.Refinement.Seq.Check
import {ns}.Defs
import {ns}.SeqStates

/-!
# The certificate of {name}'s sequence refinement

The storages of `SeqStates.lean`, with the deployed storage `s` as level 0, are
{variant}.
`seqNext s` turns a call's observable into the next call's storage list: every
slot of `seqKeys` or of the deployed storage whose final value is nonzero or that
the constructor wrote. The check runs every clean call from every storage of the
certificate, {seq_calls} calls, in {seq_parts} part(s), and every dirty call once
per storage.
-/

namespace {ns}

open SolidCore.Refinement SolidCore.Refinement.Abi SolidCore.Solidity

/-- The storage list the next call starts from. -/
def seqNext (s : List (Nat × Nat)) : Observable → List (Nat × Nat) :=
  Seq.canon (Seq.normKeys (seqKeys ++ s.map (·.1))) (s.map (·.1))

/-- The certificate's levels, the deployed storage `s` alone at level 0. -/
def seqLevelsOf (s : List (Nat × Nat)) : List (List (List (Nat × Nat))) := [s] :: seqLevels

/-- Whether the certificate is closed under every call. -/
def seqClosed : Bool := {"true" if seq_closed else "false"}

/-- The number of parts the check runs in. -/
def seqParts : Nat := {seq_parts}

/-- Whether every `seqParts`-th clean call of the certificate, from the `i`-th, checks. -/
def seqPartOk (i : Nat) : Bool :=
  match contract? with
  | .ok c =>
    match deployedStorage fuel c with
    | some s =>
      checkPart (Seq.itemOk fuel c code (seqNext s) (seqLevelsOf s) seqClosed)
        (Seq.items fns (seqLevelsOf s)).toArray seqParts i
    | none => false
  | .error _ => false

/-- Whether the dirty calls from every storage of the certificate check. -/
def seqDirtyOk : Bool :=
  match contract? with
  | .ok c =>
    match deployedStorage fuel c with
    | some s => (Seq.states (seqLevelsOf s)).all (Seq.dirtyOk (seqNext s) (seqLevelsOf s) seqClosed)
    | none => false
  | .error _ => false

theorem seqDirtyOk_eq_true : seqDirtyOk = true := by native_decide

end {ns}
""")

    for i in range(seq_parts):
        (out / module / f"SeqPart{i}.lean").write_text(f"""{header}
import {ns}.SeqDefs

namespace {ns}

theorem seqPart{i} : seqPartOk {i} = true := by native_decide

end {ns}
""")

    seq_imports = "\n".join([f"import {ns}", f"import {ns}.SeqDefs"]
                            + [f"import {ns}.SeqPart{i}" for i in range(seq_parts)])
    seq_cases = "\n".join(f"  | {i}, _ => seqPart{i}" for i in range(seq_parts))
    if seq_closed:
        seq_stmt = "RefinesSeq fuel c code (seqNext s) s (Seq.fullMsg fns)"
        seq_apply = "Seq.refinesSeq_of_cert (levels := seqLevelsOf s) (next := seqNext s) hs ⟨[s], List.mem_cons_self, List.mem_singleton_self s⟩"
        seq_doc = "every finite sequence of calls"
        seq_tail = "      exact h"
    else:
        seq_stmt = f"RefinesSeqUpTo fuel c code (seqNext s) s (Seq.fullMsg fns) {seq_depth}"
        seq_apply = "Seq.refinesSeqUpTo_of_cert (levels := seqLevelsOf s) (next := seqNext s) hs (List.mem_singleton_self s)"
        seq_doc = f"every sequence of at most {seq_depth} calls"
        seq_tail = (f"      have hl : (seqLevelsOf s).length = {seq_depth} := rfl\n"
                    "      rw [hl] at h\n      exact h")
    (out / module / "Seq.lean").write_text(f"""{header}
{seq_imports}

/-!
# {name}: solar's bytecode refines SolidCore's `Main` on sequences of calls

`refines_seq` proves that on {seq_doc} from the deployed storage, each
call of any function of `Main` in `{source}` on any argument words below
`2 ^ 256` with no value, and each starting from the storage the previous call
left, SolidCore and solar's bytecode on EthLib finish every call with the same
observables (`SolidCore.Refinement.RefinesSeq`).

The certificate of reached storages is {variant}.
Its clean calls run in both semantics by `native_decide` (which trusts Lean's
compiler), in `SeqPartI.lean`; its dirty calls reuse `Dirty.run_dirty` and
`target_dirty`, which hold from every storage, with one `native_decide` check of
the storages they keep (`seqDirtyOk_eq_true`).
-/

namespace {ns}

open SolidCore.Refinement SolidCore.Refinement.Abi

theorem seq_parts_ok : ∀ i < seqParts, seqPartOk i = true := fun i hi =>
  match i, hi with
{seq_cases}
  | n + {seq_parts}, h => absurd h (by simp only [seqParts]; omega)

/-- solar's runtime bytecode of `Main` refines SolidCore's `Main` on {seq_doc}
of every function on any argument words from the deployed storage. -/
theorem refines_seq : ∃ c s, contract? = .ok c ∧ deployedStorage fuel c = some s ∧
    {seq_stmt} := by
  have h0 := seq_parts_ok 0 (by decide)
  have hd := seqDirtyOk_eq_true
  match hc : contract?, h0, hd with
  | .ok c, h0, hd =>
    match hs : deployedStorage fuel c with
    | some s =>
      have hsh := shapeOk_eq_true
      simp only [shapeOk, hc] at hsh
      refine ⟨c, s, rfl, hs, ?_⟩
      have h := {seq_apply}
        (all_of_parts (parts := seqParts) (by decide) fun i hi => by
          simpa only [seqPartOk, seqClosed, hc, hs] using seq_parts_ok i hi)
        (by simpa only [seqDirtyOk, seqClosed, hc, hs] using hd) hsh target_dirty
{seq_tail}
    | none => simp [seqPartOk, hc, hs] at h0
  | .error _, h0, _ => simp [seqPartOk, hc] at h0

end {ns}
""")
    print(f"{source} -> {out}/{module}/Seq.lean ({'closed' if seq_closed else f'depth {seq_depth}'}, "
          f"{seq_states} storage(s), {seq_calls} calls, {seq_parts} part(s))")

seq_mods = sorted(p.parent.name for p in out.glob("*/Seq.lean"))
Path("SolidCore/Refinement/Seq").mkdir(parents=True, exist_ok=True)
Path("SolidCore/Refinement/Seq/Corpus.lean").write_text(
    "-- Generated by scripts/refinement/gen_proof.py. Do not edit.\n\n"
    "import SolidCore.Refinement.Sequence\n"
    + "".join(f"import SolidCore.Refinement.Corpus.{m}.Seq\n" for m in seq_mods)
    + "\n/-! The sequence refinement proofs of every contract in scripts/refinement/corpus/\n"
    "that has one: `Corpus/<C>/Seq.lean`. -/\n")
