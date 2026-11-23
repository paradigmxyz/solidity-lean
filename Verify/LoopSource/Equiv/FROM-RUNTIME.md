# solidCoreRuntime vs solidCoreFrom: why no bridge exists for Counter

**Verdict: not provable in Verify/LoopSource/** (for Counter it is false).

`Generic.Expected` states equivalence over `Source.semAt src ctx = solidCoreFrom ctx.caller src.fuel`
(`Verify/Generic/Expected.lean:90`). Its run, `Source.resultFrom?`
(`SolidCore/Refinement/Generic/StageFrom.lean:33-35`), first runs the constructor with **no
arguments**:

    TypeCheck.CheckedContract.constructWithContext? fuel contract context State.empty selfAddress 0 []

and returns `none` unless that returns. Counter's constructor is `constructor(uint256 _limit)`. On
the run's own checked contract (`Certified/CounterRun/Source.lean`, solc 0.8.35 translation of
Counter.sol f1c87a33…) the evaluator gives (`FromScratch.lean.txt`, `lake env lean`, not a kernel proof):

    constructWithContext? 4096 c … []                        = none
    Source.runFrom callerAddress 4096 c (bump(1), limit 8)   = none
    Generic.Loop.runtimeRun 4096 c (bump(1), limit 8)        = some (success = true)

So under `solidCoreFrom`, Counter has no run on any call (the constructor's context differs per
call only in `value`). `EquivAt` then needs every bytecode result on a valid call to be `Inert`
(`success = false`, storage unchanged, no logs), but the emitted runtime succeeds on `bump(1)`.
No hypothesis that is true of Counter turns `Shapes.Equiv (solidCoreRuntime fuel)` into the
`solidCoreFrom` conjunct.

## The missing piece (outside this lane)

A source semantics that constructs with the deployment's arguments, and an acceptance statement
that uses it:

1. `SolidCore/Refinement/Generic/StageFrom.lean:35` (and `Statement.lean:85`): `resultFrom?` takes
   constructor argument values `args : List TypeCheck.CoreValue` in place of `[]`, e.g.
   `resultFromArgs? caller fuel args contract call`, with `solidCoreFromArgs caller fuel args : Sem`
   and `solidCoreFromArgs a fuel [] = solidCoreFrom a fuel` by `rfl`.
2. `Verify/Generic/Expected.lean:65,90`: `Source` carries `ctorArgs` (default `[]`) and
   `Source.semAt src ctx := solidCoreFromArgs ctx.caller src.fuel src.ctorArgs`.
3. Then the bridge this lane can prove: for a contract whose constructor on `args` returns a
   state `d` that is `State.empty` except for `d.storage`, and calls whose storage holds every
   key `d.storage` sets (the deployed storage the bytecode also starts from),
   `solidCoreFromArgs callerAddress fuel args` and `solidCoreRuntime fuel` agree, so
   `Shapes.Equiv (solidCoreRuntime fuel) c code Valid → EquivAt (solidCoreFromArgs …) c Context.default code Valid`.
   For callers other than `callerAddress`, `runtimeRun` (`LoopRun.lean:27-39`) fixes the sender to
   `callerAddress` too, so it would also need a caller parameter (or the statement restricted to
   `Context.default`).

The lifecycle route already constructs with arguments (`Verify/Lifecycle/Route.lean:48-64`,
`deployedAtWith fuel c (wordArgs ws) s`), so items 1–3 would reuse its constructor run.
