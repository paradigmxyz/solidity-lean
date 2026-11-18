import Verify.Generic.CtorArgs.Gates


/-!
# Exact types and axioms of the constructor-arguments interface

Each `#check` pins a definition's or theorem's exact type and each `#print axioms` its axioms
(at most `propext`, `Classical.choice` and `Quot.sound`: no `sorryAx`, no
`Lean.ofReduceBool`), by `#guard_msgs`, so a change to either fails this module.
-/
/--
info: SolidCore.Refinement.Source.deployArgs? : ℕ →
  List ℕ → SolidCore.Solidity.TypeCheck.CheckedContract → Option SolidCore.Solidity.TypeCheck.CoreCallResult
-/
#guard_msgs in
#check @SolidCore.Refinement.Source.deployArgs?
/--
info: 'SolidCore.Refinement.Source.deployArgs?' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SolidCore.Refinement.Source.deployArgs?
/--
info: SolidCore.Refinement.Source.resultFromArgs? : ℕ →
  ℕ →
    List ℕ →
      SolidCore.Solidity.TypeCheck.CheckedContract →
        SolarTV.Call → Option SolidCore.Solidity.TypeCheck.CoreAbiCallResult
-/
#guard_msgs in
#check @SolidCore.Refinement.Source.resultFromArgs?
/--
info: 'SolidCore.Refinement.Source.resultFromArgs?' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SolidCore.Refinement.Source.resultFromArgs?
/--
info: SolidCore.Refinement.Source.resultFromArgs?_nil : ∀ (caller fuel : ℕ)
  (contract : SolidCore.Solidity.TypeCheck.CheckedContract) (call : SolarTV.Call),
  SolidCore.Refinement.Source.resultFromArgs? caller fuel [] contract call =
    SolidCore.Refinement.Source.resultFrom? caller fuel contract call
-/
#guard_msgs in
#check @SolidCore.Refinement.Source.resultFromArgs?_nil
/--
info: 'SolidCore.Refinement.Source.resultFromArgs?_nil' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SolidCore.Refinement.Source.resultFromArgs?_nil
/--
info: SolidCore.Refinement.Source.runFromArgs : ℕ →
  ℕ → List ℕ → SolidCore.Solidity.TypeCheck.CheckedContract → SolarTV.Call → Option SolarTV.Observable
-/
#guard_msgs in
#check @SolidCore.Refinement.Source.runFromArgs
/--
info: 'SolidCore.Refinement.Source.runFromArgs' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SolidCore.Refinement.Source.runFromArgs
/--
info: SolidCore.Refinement.Source.runFromArgs_nil : ∀ (caller fuel : ℕ),
  SolidCore.Refinement.Source.runFromArgs caller fuel [] = SolidCore.Refinement.Source.runFrom caller fuel
-/
#guard_msgs in
#check @SolidCore.Refinement.Source.runFromArgs_nil
/--
info: 'SolidCore.Refinement.Source.runFromArgs_nil' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SolidCore.Refinement.Source.runFromArgs_nil
/--
info: SolidCore.Refinement.solidCoreFromArgs : ℕ → ℕ → List ℕ → SolarTV.Sem
-/
#guard_msgs in
#check @SolidCore.Refinement.solidCoreFromArgs
/--
info: 'SolidCore.Refinement.solidCoreFromArgs' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SolidCore.Refinement.solidCoreFromArgs
/--
info: SolidCore.Refinement.solidCoreFromArgs_nil : ∀ (caller fuel : ℕ),
  SolidCore.Refinement.solidCoreFromArgs caller fuel [] = SolidCore.Refinement.solidCoreFrom caller fuel
-/
#guard_msgs in
#check @SolidCore.Refinement.solidCoreFromArgs_nil
/--
info: 'SolidCore.Refinement.solidCoreFromArgs_nil' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SolidCore.Refinement.solidCoreFromArgs_nil
/--
info: SolidCore.Refinement.Generic.Loop.runtimeResultFrom? : ℕ →
  ℕ →
    SolidCore.Solidity.TypeCheck.CheckedContract → SolarTV.Call → Option SolidCore.Solidity.TypeCheck.CoreAbiCallResult
-/
#guard_msgs in
#check @SolidCore.Refinement.Generic.Loop.runtimeResultFrom?
/--
info: 'SolidCore.Refinement.Generic.Loop.runtimeResultFrom?' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SolidCore.Refinement.Generic.Loop.runtimeResultFrom?
/--
info: SolidCore.Refinement.Generic.Loop.runtimeRunFrom : ℕ →
  ℕ → SolidCore.Solidity.TypeCheck.CheckedContract → SolarTV.Call → Option SolarTV.Observable
-/
#guard_msgs in
#check @SolidCore.Refinement.Generic.Loop.runtimeRunFrom
/--
info: 'SolidCore.Refinement.Generic.Loop.runtimeRunFrom' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SolidCore.Refinement.Generic.Loop.runtimeRunFrom
/--
info: SolidCore.Refinement.Generic.Loop.solidCoreRuntimeFrom : ℕ → ℕ → SolarTV.Sem
-/
#guard_msgs in
#check @SolidCore.Refinement.Generic.Loop.solidCoreRuntimeFrom
/--
info: 'SolidCore.Refinement.Generic.Loop.solidCoreRuntimeFrom' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SolidCore.Refinement.Generic.Loop.solidCoreRuntimeFrom
/--
info: SolidCore.Refinement.Generic.Loop.runtimeResult?_eq_from : ∀ (fuel : ℕ),
  SolidCore.Refinement.Generic.Loop.runtimeResult? fuel =
    SolidCore.Refinement.Generic.Loop.runtimeResultFrom? SolidCore.Refinement.callerAddress fuel
-/
#guard_msgs in
#check @SolidCore.Refinement.Generic.Loop.runtimeResult?_eq_from
/--
info: 'SolidCore.Refinement.Generic.Loop.runtimeResult?_eq_from' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SolidCore.Refinement.Generic.Loop.runtimeResult?_eq_from
/--
info: SolidCore.Refinement.Generic.Loop.runtimeRun_eq_from : ∀ (fuel : ℕ),
  SolidCore.Refinement.Generic.Loop.runtimeRun fuel =
    SolidCore.Refinement.Generic.Loop.runtimeRunFrom SolidCore.Refinement.callerAddress fuel
-/
#guard_msgs in
#check @SolidCore.Refinement.Generic.Loop.runtimeRun_eq_from
/--
info: 'SolidCore.Refinement.Generic.Loop.runtimeRun_eq_from' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SolidCore.Refinement.Generic.Loop.runtimeRun_eq_from
/--
info: SolidCore.Refinement.Generic.Loop.solidCoreRuntime_eq_from : ∀ (fuel : ℕ),
  SolidCore.Refinement.Generic.Loop.solidCoreRuntime fuel =
    SolidCore.Refinement.Generic.Loop.solidCoreRuntimeFrom SolidCore.Refinement.callerAddress fuel
-/
#guard_msgs in
#check @SolidCore.Refinement.Generic.Loop.solidCoreRuntime_eq_from
/--
info: 'SolidCore.Refinement.Generic.Loop.solidCoreRuntime_eq_from' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SolidCore.Refinement.Generic.Loop.solidCoreRuntime_eq_from
/--
info: SolidCore.Refinement.Generic.deployArgs?_eq_lifecycle : ∀ (fuel : ℕ) (ws : List ℕ)
  (c : SolidCore.Solidity.TypeCheck.CheckedContract),
  SolidCore.Refinement.Source.deployArgs? fuel ws c =
    SolidCore.Solidity.TypeCheck.CheckedContract.constructWithContext? fuel c (SolidCore.Refinement.Wide.ctxOf c)
      SolidCore.Solidity.Source.State.empty SolidCore.Refinement.selfAddress 0 (Verify.Lifecycle.wordArgs ws)
-/
#guard_msgs in
#check @SolidCore.Refinement.Generic.deployArgs?_eq_lifecycle
/--
info: 'SolidCore.Refinement.Generic.deployArgs?_eq_lifecycle' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SolidCore.Refinement.Generic.deployArgs?_eq_lifecycle
/--
info: SolidCore.Refinement.Generic.deployedAtWith_eq : ∀ (fuel : ℕ) (ws : List ℕ)
  (c : SolidCore.Solidity.TypeCheck.CheckedContract) (s : List (ℕ × ℕ)),
  Verify.Lifecycle.deployedAtWith fuel c (Verify.Lifecycle.wordArgs ws) s =
    match SolidCore.Refinement.Source.deployArgs? fuel ws c with
    | some (SolidCore.Solidity.Source.CallResult.returned d a) => Std.HashMap.toList d.storage == s && d.events.isEmpty
    | x => false
-/
#guard_msgs in
#check @SolidCore.Refinement.Generic.deployedAtWith_eq
/--
info: 'SolidCore.Refinement.Generic.deployedAtWith_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SolidCore.Refinement.Generic.deployedAtWith_eq
/--
info: @SolidCore.Refinement.Generic.deployedAtWith_iff : ∀ {fuel : ℕ} {ws : List ℕ}
  {c : SolidCore.Solidity.TypeCheck.CheckedContract} {d : SolidCore.Solidity.Source.State} {s : List (ℕ × ℕ)},
  Verify.Lifecycle.DeployedAtWith fuel c (Verify.Lifecycle.wordArgs ws) d s ↔
    (∃ vs,
        SolidCore.Refinement.Source.deployArgs? fuel ws c = some (SolidCore.Solidity.Source.CallResult.returned d vs)) ∧
      Std.HashMap.toList d.storage = s ∧ d.events = []
-/
#guard_msgs in
#check @SolidCore.Refinement.Generic.deployedAtWith_iff
/--
info: 'SolidCore.Refinement.Generic.deployedAtWith_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SolidCore.Refinement.Generic.deployedAtWith_iff
/--
info: @SolidCore.Refinement.Generic.resultFromArgs?_of_deployedAtWith : ∀ {fuel : ℕ} {ws : List ℕ}
  {c : SolidCore.Solidity.TypeCheck.CheckedContract} {d : SolidCore.Solidity.Source.State} {s : List (ℕ × ℕ)},
  Verify.Lifecycle.DeployedAtWith fuel c (Verify.Lifecycle.wordArgs ws) d s →
    ∀ (caller : ℕ) (call : SolarTV.Call),
      SolidCore.Refinement.Source.resultFromArgs? caller fuel ws c call =
        SolidCore.Solidity.TypeCheck.CheckedContract.callCalldataAtFromWithContext? fuel c
          (have __src := SolidCore.Solidity.Source.Contract.context c.core;
          { storageFields := __src.storageFields, immutableFields := __src.immutableFields,
            selfDispatch? := __src.selfDispatch?, eventDecls := __src.eventDecls, errorDecls := __src.errorDecls,
            checked := __src.checked, construction := __src.construction, calldata := __src.calldata,
            sender := SolidCore.Refinement.callerAddress, value := call.callvalue,
            self := SolidCore.Refinement.selfAddress, accountBalances := __src.accountBalances,
            accountCodes := __src.accountCodes, accountCodehashes := __src.accountCodehashes,
            contractAddresses := __src.contractAddresses, contractCreationCodes := __src.contractCreationCodes,
            contractRuntimeCodes := __src.contractRuntimeCodes, blockEnv := __src.blockEnv, txEnv := __src.txEnv,
            evmVersion := __src.evmVersion, createdInTransactionAccounts := __src.createdInTransactionAccounts,
            gasleft := __src.gasleft, memoryAllocationLimit? := __src.memoryAllocationLimit? })
          { storage := List.foldl (fun acc kv => acc.insertLoop kv.1 kv.2) d.storage call.storage,
            transient := d.transient, immutables := d.immutables, selfdestructs := d.selfdestructs,
            selfdestructEffects := d.selfdestructEffects, externalInteractions := d.externalInteractions,
            selfBalance := d.selfBalance, selfNonce := d.selfNonce, events := d.events, envWorld? := d.envWorld?,
            worldMutatedSinceAdoption := d.worldMutatedSinceAdoption, adoptedLogPrefix := d.adoptedLogPrefix,
            adoptedEventCount := d.adoptedEventCount, adoptedSelfdestructCount := d.adoptedSelfdestructCount }
          SolidCore.Refinement.selfAddress caller call.callvalue (List.map (fun x => x.toNat) call.calldata.data.toList)
-/
#guard_msgs in
#check @SolidCore.Refinement.Generic.resultFromArgs?_of_deployedAtWith
/--
info: 'SolidCore.Refinement.Generic.resultFromArgs?_of_deployedAtWith' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SolidCore.Refinement.Generic.resultFromArgs?_of_deployedAtWith
/--
info: @SolidCore.Refinement.Generic.runFromArgs_eq_none : ∀ {fuel : ℕ} {ws : List ℕ}
  {c : SolidCore.Solidity.TypeCheck.CheckedContract},
  (∀ (d : SolidCore.Solidity.Source.State) (vs : List SolidCore.Solidity.Source.Value),
      SolidCore.Refinement.Source.deployArgs? fuel ws c ≠ some (SolidCore.Solidity.Source.CallResult.returned d vs)) →
    ∀ (caller : ℕ) (call : SolarTV.Call), SolidCore.Refinement.Source.runFromArgs caller fuel ws c call = none
-/
#guard_msgs in
#check @SolidCore.Refinement.Generic.runFromArgs_eq_none
/--
info: 'SolidCore.Refinement.Generic.runFromArgs_eq_none' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SolidCore.Refinement.Generic.runFromArgs_eq_none
/--
info: SolidCore.Refinement.Generic.wordsOf : ℕ → List UInt8 → List ℕ
-/
#guard_msgs in
#check @SolidCore.Refinement.Generic.wordsOf
/--
info: 'SolidCore.Refinement.Generic.wordsOf' does not depend on any axioms
-/
#guard_msgs in
#print axioms SolidCore.Refinement.Generic.wordsOf
/--
info: SolidCore.Refinement.Generic.argBytes_toList : ∀ (ws : List ℕ),
  (Verify.Lifecycle.argBytes ws).data.toList = List.flatMap (fun w => EthLib.Base.natToBytes 32 w) ws
-/
#guard_msgs in
#check @SolidCore.Refinement.Generic.argBytes_toList
/--
info: 'SolidCore.Refinement.Generic.argBytes_toList' does not depend on any axioms
-/
#guard_msgs in
#print axioms SolidCore.Refinement.Generic.argBytes_toList
/--
info: SolidCore.Refinement.Generic.wordsOf_flatMap : ∀ (ws : List ℕ),
  (∀ w ∈ ws, w < 2 ^ 256) →
    ∀ (rest : List UInt8),
      SolidCore.Refinement.Generic.wordsOf ws.length (List.flatMap (fun w => EthLib.Base.natToBytes 32 w) ws ++ rest) =
        ws
-/
#guard_msgs in
#check @SolidCore.Refinement.Generic.wordsOf_flatMap
/--
info: 'SolidCore.Refinement.Generic.wordsOf_flatMap' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SolidCore.Refinement.Generic.wordsOf_flatMap
/--
info: SolidCore.Refinement.Generic.ArgsBound : ByteArray → ByteArray → List ℕ → Prop
-/
#guard_msgs in
#check @SolidCore.Refinement.Generic.ArgsBound
/--
info: 'SolidCore.Refinement.Generic.ArgsBound' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms SolidCore.Refinement.Generic.ArgsBound
/--
info: @SolidCore.Refinement.Generic.ArgsBound.size : ∀ {initcode creation : ByteArray} {ws : List ℕ},
  SolidCore.Refinement.Generic.ArgsBound initcode creation ws → creation.size = initcode.size + 32 * ws.length
-/
#guard_msgs in
#check @SolidCore.Refinement.Generic.ArgsBound.size
/--
info: 'SolidCore.Refinement.Generic.ArgsBound.size' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms SolidCore.Refinement.Generic.ArgsBound.size
/--
info: @SolidCore.Refinement.Generic.ArgsBound.decode : ∀ {initcode creation : ByteArray} {ws : List ℕ},
  SolidCore.Refinement.Generic.ArgsBound initcode creation ws →
    SolidCore.Refinement.Generic.wordsOf ((creation.size - initcode.size) / 32)
        (List.drop initcode.size creation.data.toList) =
      ws
-/
#guard_msgs in
#check @SolidCore.Refinement.Generic.ArgsBound.decode
/--
info: 'SolidCore.Refinement.Generic.ArgsBound.decode' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SolidCore.Refinement.Generic.ArgsBound.decode
/--
info: @SolidCore.Refinement.Generic.ArgsBound.unique : ∀ {initcode creation : ByteArray} {ws ws' : List ℕ},
  SolidCore.Refinement.Generic.ArgsBound initcode creation ws →
    SolidCore.Refinement.Generic.ArgsBound initcode creation ws' → ws = ws'
-/
#guard_msgs in
#check @SolidCore.Refinement.Generic.ArgsBound.unique
/--
info: 'SolidCore.Refinement.Generic.ArgsBound.unique' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SolidCore.Refinement.Generic.ArgsBound.unique
/--
info: @SolidCore.Verify.Generic.Source : optParam (List ℕ) [] → Type
-/
#guard_msgs in
#check @SolidCore.Verify.Generic.Source
/--
info: 'SolidCore.Verify.Generic.Source' does not depend on any axioms
-/
#guard_msgs in
#print axioms SolidCore.Verify.Generic.Source
/--
info: @SolidCore.Verify.Generic.Source.ctorArgs : {ws : List ℕ} → SolidCore.Verify.Generic.Source ws → List ℕ
-/
#guard_msgs in
#check @SolidCore.Verify.Generic.Source.ctorArgs
/--
info: 'SolidCore.Verify.Generic.Source.ctorArgs' does not depend on any axioms
-/
#guard_msgs in
#print axioms SolidCore.Verify.Generic.Source.ctorArgs
/--
info: @SolidCore.Verify.Generic.Source.withArgs : {ws₀ : List ℕ} →
  SolidCore.Verify.Generic.Source ws₀ → (ws : List ℕ) → SolidCore.Verify.Generic.Source ws
-/
#guard_msgs in
#check @SolidCore.Verify.Generic.Source.withArgs
/--
info: 'SolidCore.Verify.Generic.Source.withArgs' does not depend on any axioms
-/
#guard_msgs in
#print axioms SolidCore.Verify.Generic.Source.withArgs
/--
info: @SolidCore.Verify.Generic.Source.semAt : {ws : List ℕ} →
  SolidCore.Verify.Generic.Source ws → SolidCore.Verify.Generic.Context → SolarTV.Sem
-/
#guard_msgs in
#check @SolidCore.Verify.Generic.Source.semAt
/--
info: 'SolidCore.Verify.Generic.Source.semAt' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SolidCore.Verify.Generic.Source.semAt
/--
info: SolidCore.Verify.Generic.Source.semAt_nil : ∀ (src : SolidCore.Verify.Generic.Source)
  (ctx : SolidCore.Verify.Generic.Context), src.semAt ctx = SolidCore.Refinement.solidCoreFrom ctx.caller (src.fuel [])
-/
#guard_msgs in
#check @SolidCore.Verify.Generic.Source.semAt_nil
/--
info: 'SolidCore.Verify.Generic.Source.semAt_nil' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SolidCore.Verify.Generic.Source.semAt_nil
/--
info: @SolidCore.Verify.Generic.Source.semAt_withArgs : ∀ {ws₀ : List ℕ} (src : SolidCore.Verify.Generic.Source ws₀)
  (ws : List ℕ) (ctx : SolidCore.Verify.Generic.Context),
  (src.withArgs ws).semAt ctx = SolidCore.Refinement.solidCoreFromArgs ctx.caller src.fuel ws
-/
#guard_msgs in
#check @SolidCore.Verify.Generic.Source.semAt_withArgs
/--
info: 'SolidCore.Verify.Generic.Source.semAt_withArgs' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SolidCore.Verify.Generic.Source.semAt_withArgs
/--
info: @SolidCore.Verify.Generic.Expected : {ws : List ℕ} →
  SolidCore.Verify.Generic.Source ws → SolidCore.Verify.Generic.Spec → List ℕ → Prop
-/
#guard_msgs in
#check @SolidCore.Verify.Generic.Expected
/--
info: 'SolidCore.Verify.Generic.Expected' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SolidCore.Verify.Generic.Expected
/--
info: @SolidCore.Verify.Generic.Source.CreatedBy : {ws : List ℕ} →
  SolidCore.Verify.Generic.Source ws → ByteArray → ByteArray → Prop
-/
#guard_msgs in
#check @SolidCore.Verify.Generic.Source.CreatedBy
/--
info: 'SolidCore.Verify.Generic.Source.CreatedBy' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms SolidCore.Verify.Generic.Source.CreatedBy
/--
info: @SolidCore.Verify.Generic.Source.CreatedBy.unique : ∀ {ws ws' : List ℕ} {src : SolidCore.Verify.Generic.Source ws}
  {src' : SolidCore.Verify.Generic.Source ws'} {initcode creation : ByteArray},
  src.CreatedBy initcode creation → src'.CreatedBy initcode creation → src.ctorArgs = src'.ctorArgs
-/
#guard_msgs in
#check @SolidCore.Verify.Generic.Source.CreatedBy.unique
/--
info: 'SolidCore.Verify.Generic.Source.CreatedBy.unique' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SolidCore.Verify.Generic.Source.CreatedBy.unique
/--
info: @SolidCore.Verify.Generic.Source.run_of_statement : ∀ {ws : List ℕ} {src : SolidCore.Verify.Generic.Source ws}
  {c : SolidCore.Solidity.TypeCheck.CheckedContract} {initcode code creation : ByteArray} {s : List (ℕ × ℕ)},
  src.CreatedBy initcode creation →
    Verify.Lifecycle.Statement src.fuel c initcode code ws s →
      SolidCore.Refinement.Deploys creation code s ∧
        ∃ d,
          Std.HashMap.toList d.storage = s ∧
            ∀ (ctx : SolidCore.Verify.Generic.Context) (call : SolarTV.Call),
              (src.semAt ctx).run c call =
                Option.map (SolidCore.Refinement.Source.observe call)
                  (SolidCore.Solidity.TypeCheck.CheckedContract.callCalldataAtFromWithContext? src.fuel c
                    (have __src := SolidCore.Solidity.Source.Contract.context c.core;
                    { storageFields := __src.storageFields, immutableFields := __src.immutableFields,
                      selfDispatch? := __src.selfDispatch?, eventDecls := __src.eventDecls,
                      errorDecls := __src.errorDecls, checked := __src.checked, construction := __src.construction,
                      calldata := __src.calldata, sender := SolidCore.Refinement.callerAddress, value := call.callvalue,
                      self := SolidCore.Refinement.selfAddress, accountBalances := __src.accountBalances,
                      accountCodes := __src.accountCodes, accountCodehashes := __src.accountCodehashes,
                      contractAddresses := __src.contractAddresses,
                      contractCreationCodes := __src.contractCreationCodes,
                      contractRuntimeCodes := __src.contractRuntimeCodes, blockEnv := __src.blockEnv,
                      txEnv := __src.txEnv, evmVersion := __src.evmVersion,
                      createdInTransactionAccounts := __src.createdInTransactionAccounts, gasleft := __src.gasleft,
                      memoryAllocationLimit? := __src.memoryAllocationLimit? })
                    { storage := List.foldl (fun acc kv => acc.insertLoop kv.1 kv.2) d.storage call.storage,
                      transient := d.transient, immutables := d.immutables, selfdestructs := d.selfdestructs,
                      selfdestructEffects := d.selfdestructEffects, externalInteractions := d.externalInteractions,
                      selfBalance := d.selfBalance, selfNonce := d.selfNonce, events := d.events,
                      envWorld? := d.envWorld?, worldMutatedSinceAdoption := d.worldMutatedSinceAdoption,
                      adoptedLogPrefix := d.adoptedLogPrefix, adoptedEventCount := d.adoptedEventCount,
                      adoptedSelfdestructCount := d.adoptedSelfdestructCount }
                    SolidCore.Refinement.selfAddress ctx.caller call.callvalue
                    (List.map (fun x => x.toNat) call.calldata.data.toList))
-/
#guard_msgs in
#check @SolidCore.Verify.Generic.Source.run_of_statement
/--
info: 'SolidCore.Verify.Generic.Source.run_of_statement' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SolidCore.Verify.Generic.Source.run_of_statement
/--
info: Verify.Generic.CtorArgs.nilSame_eq : Verify.Generic.CtorArgs.nilSame? = true
-/
#guard_msgs in
#check @Verify.Generic.CtorArgs.nilSame_eq
/--
info: 'Verify.Generic.CtorArgs.nilSame_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Verify.Generic.CtorArgs.nilSame_eq
/--
info: Verify.Generic.CtorArgs.argTwo_eq : Verify.Generic.CtorArgs.argTwo? = true
-/
#guard_msgs in
#check @Verify.Generic.CtorArgs.argTwo_eq
/--
info: 'Verify.Generic.CtorArgs.argTwo_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Verify.Generic.CtorArgs.argTwo_eq
/--
info: Verify.Generic.CtorArgs.argChanged_eq : Verify.Generic.CtorArgs.argChanged? = false
-/
#guard_msgs in
#check @Verify.Generic.CtorArgs.argChanged_eq
/--
info: 'Verify.Generic.CtorArgs.argChanged_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Verify.Generic.CtorArgs.argChanged_eq
/--
info: Verify.Generic.CtorArgs.argMissing_eq : Verify.Generic.CtorArgs.argMissing? = true
-/
#guard_msgs in
#check @Verify.Generic.CtorArgs.argMissing_eq
/--
info: 'Verify.Generic.CtorArgs.argMissing_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Verify.Generic.CtorArgs.argMissing_eq
/--
info: Verify.Generic.CtorArgs.argWrong_eq : Verify.Generic.CtorArgs.argWrong? = true
-/
#guard_msgs in
#check @Verify.Generic.CtorArgs.argWrong_eq
/--
info: 'Verify.Generic.CtorArgs.argWrong_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Verify.Generic.CtorArgs.argWrong_eq
/--
info: Verify.Generic.CtorArgs.argExtra_eq : Verify.Generic.CtorArgs.argExtra? = true
-/
#guard_msgs in
#check @Verify.Generic.CtorArgs.argExtra_eq
/--
info: 'Verify.Generic.CtorArgs.argExtra_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Verify.Generic.CtorArgs.argExtra_eq
/--
info: Verify.Generic.CtorArgs.ownRevert_eq : Verify.Generic.CtorArgs.ownRevert? = true
-/
#guard_msgs in
#check @Verify.Generic.CtorArgs.ownRevert_eq
/--
info: 'Verify.Generic.CtorArgs.ownRevert_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Verify.Generic.CtorArgs.ownRevert_eq
/--
info: Verify.Generic.CtorArgs.collide_eq : Verify.Generic.CtorArgs.collide? = true
-/
#guard_msgs in
#check @Verify.Generic.CtorArgs.collide_eq
/--
info: 'Verify.Generic.CtorArgs.collide_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Verify.Generic.CtorArgs.collide_eq
/--
info: Verify.Generic.CtorArgs.ownCaller_eq : Verify.Generic.CtorArgs.ownCaller? = true
-/
#guard_msgs in
#check @Verify.Generic.CtorArgs.ownCaller_eq
/--
info: 'Verify.Generic.CtorArgs.ownCaller_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Verify.Generic.CtorArgs.ownCaller_eq
/--
info: Verify.Generic.CtorArgs.ownDeployerIsCaller_eq : Verify.Generic.CtorArgs.ownDeployerIsCaller? = false
-/
#guard_msgs in
#check @Verify.Generic.CtorArgs.ownDeployerIsCaller_eq
/--
info: 'Verify.Generic.CtorArgs.ownDeployerIsCaller_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Verify.Generic.CtorArgs.ownDeployerIsCaller_eq
/--
info: Verify.Generic.CtorArgs.semAt_ctx_differ : Verify.Generic.CtorArgs.obs? Verify.Generic.CtorArgs.ownU "OwnedCtor"
    [42, 48879] 48879 ≠
  Verify.Generic.CtorArgs.obs? Verify.Generic.CtorArgs.ownU "OwnedCtor" [42, 48879] SolidCore.Refinement.callerAddress
-/
#guard_msgs in
#check @Verify.Generic.CtorArgs.semAt_ctx_differ
/--
info: 'Verify.Generic.CtorArgs.semAt_ctx_differ' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Verify.Generic.CtorArgs.semAt_ctx_differ

