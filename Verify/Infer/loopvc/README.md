# Loop certificates from solar-verify's loop-cut export

This directory checks, in the Lean kernel, the loop obligations of any function with one loop
that `solar-verify --emit-loopvc` exports (format 1, docs/loopvc-interface.md in solar): the
invariant holds on entry (initiation), the loop body keeps it (every back edge) and lowers the
ranking function (termination), and the exit paths meet what follows the loop (exit and outcome).
The same checker runs on every such function; nothing is specific to one contract.

    solar-verify --no-infer --dry-run --emit-loopvc EXPORT FILE.sol     # from the repository root
    Verify/Infer/loopvc/run.sh EXPORT OUT [TIMEOUT_SECONDS]              # exit 0 proved, 3 blocked, 1 failed

`run.sh` plans every unit with a loop (`loopcert.py plan`), writes a certificate
`LoopCert.<C>.<f>` per required unit (`loopcert.py gen`), compiles the exported interface library,
the unit's obligation module and its loop-cut module, compiles the certificate with lean-smt's
cvc5 reconstruction (`Verify/Discharge/Reconstruct`), reads the axioms of its theorem `certified`,
runs `Verify/Discharge/discharge.sh` on the whole export as an independent per-obligation audit
(axioms and vacuity), and writes `OUT/receipt.json` (`loopcert.py receipt`).

## What a certificate proves

For each template `tK` on the cut's entry, back and exit edges, the generated file proves every
instance obligation by `vc_smt` and `tK.Valid cut cand` through the exporter's `tK_valid` (whose
`tK_exact` is `rfl`: the template instantiated at the run's candidate is exactly the unit's
obligations). `certified` is the conjunction over every template; `obligations_valid` is the same
as one list of `Obligation.Valid` facts. A unit is **proved** only when the certificate builds,
`certified` depends on no axiom beyond `propext`, `Classical.choice` and `Quot.sound`, and the
discharge audit proves each instance with none vacuous. Anything else (an obligation that does not
hold, a timeout, a module the kernel rejects, a missing axiom report) is **failed**, never proved.

## How it connects to the code

`Bridge.lean` states the connection to SolidCore's loop rule (`ForCert` / `WhileCert` of
`SolidCore/Refinement/Generic/Loop.lean`): a per-loop binding `ForBinds` / `WhileBinds` (valid
obligations make the candidate a ranking certificate of the SolidCore loop), and
`forLoop_of_cut` / `whileLoop_of_cut`, which give the loop's end in SolidCore's interpreter from a
binding and `obligations_valid`. The binding is the loop analogue of `Binds`
(`Verify/VC/Obligations.lean`): one proof per function. **It is not generated yet**: today a loop
certificate is a kernel-checked fact about solar-verify's encoding of the function, and the
source-to-bytecode theorem of a function with a loop still needs its binding (verify_counter's
`bump` has a hand-written one, `Contracts/VerifyCounter/SourceLoop.lean`). The generic
`EndToEnd` path (`bytecode_of_checked`) covers loop-free functions only: `eraseFn` erases to a
`Tree` of `halt` and `ite`.

## Invariants

Invariants and ranking functions come from the source's annotations or from a certify-invariants
file; nothing is inferred (the exporter runs with `--no-infer`). A supplied candidate is checked
exactly like an annotated one: it is an input to the proof, not trusted.

    {"format": "certify-invariants", "version": 1,
     "loops": [{"function": "C.f", "line": L, "invariants": ["i <= n", "..."], "decreases": "n - i"}]}

`loopcert.py annotate SOURCE INVARIANTS OUT` writes OUT with each entry's lines inserted as
`/// @custom:invariant` and `/// @custom:decreases` comments right above line L, and checks that
deleting the inserted lines gives SOURCE byte for byte; comments do not change the compiled code
(`tests/test.sh` compares the runtime bytecode of both).

## Supported and blocked

Required (certified): a function with exactly one `for` or `while` loop, at least one invariant,
exactly one `decreases`, no call inside the loop, an exit edge to a normal return, and every
required obligation of the function an instance of exactly one template. Internal calls outside
the loop are part of solar-verify's encoding of the function (their requirements become path
obligations like any other) and need nothing here.

**Blocked** (status `blocked`, exit 3, with the reason; the driver must not report such a function
as certified):

* a call inside the loop: no call summaries in format 1 (the exporter reports the call edge);
* two or more loops in a function, nested or in sequence;
* no `decreases` (termination has no proof) or more than one;
* no invariant;
* an export whose files do not match the hashes the cut names (`LoopVc.lean`, the Horn view), or
  a run that reports errors (a source outside the run's directory);
* required queries that are not instances of the cut's templates.

## Tests

    SOLAR_VERIFY=.../solar-verify SOLC=.../solc Verify/Infer/loopvc/tests/test.sh WORKDIR

Ten cases: verify_counter's `bump` (a `for` loop with annotations) and the held-out
`tests/heldout/Drain.sol` (a `while` loop counting down with a local accumulator and a named
return, written for these tests, with its invariants supplied in `Drain.invariants.json`) proved;
the annotated copy's bytecode equal to the source's; a supplied invariant that is not preserved
failed; no `decreases` blocked; a call in the loop and two loops blocked; a candidate edited in the
exported template module failed (the kernel rejects `tK_exact`); an edited Horn view blocked.
