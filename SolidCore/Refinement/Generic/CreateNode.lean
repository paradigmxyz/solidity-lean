import SolidCore.Solidity.Interpreter
import EthLib.Execution.Evm.Call.ContractAddress

/-!
# The create node of SolidCore's source semantics

`eval_create2Bytes`: inline assembly's `create2(value, add(code, 32), mload(code), salt)`
(`Expr.create2Bytes`), whose operands evaluate without a request, evaluates to one request node:
the CREATE2 of the sent world (`snapshotWorld`) from the contract, with the bytes of `code` as
init code (`create2BytesRequest`), continued by the answered address as a word and the adopted
world. It is the source-side piece a source-to-MIR check of a function with CREATE2 (as
UniswapV2Factory.createPair) composes, as `CallNode.eval_tryCall` is for calls.

What the environment answers is the open world's: `EvmCreate2 req resp` says the answer is the
EVM's, the address 0 (a failed creation) or EIP-1014's address of the request's creator, salt and
init code (`create2Word`, by EthLib's `create2Address` and its Keccak-256), so `answer_word`
gives the address `create2Bytes` returns under such an environment. The premise is about the
environment, never about the hash: it names no collision freedom.
-/

namespace SolidCore.Refinement.CreateNode

open SolidCore.Solidity.Source EvmCompiler.Simulation

theorem ibind_pure {ε α β : Type} (a : α) (f : α → Interaction ε β) :
    (Interaction.pure a).bind f = f a := rfl

theorem ibind_done {ε α β : Type} (a : α) (f : α → Interaction ε β) :
    (Interaction.done (Except.ok a)).bind f = f a := rfl

/-- **The create node**: CREATE2 of the evaluated init code asks one creation of the sent world
and returns the answered address as a word, with the adopted world. Yul evaluates the salt,
then the init code, then the value. -/
theorem eval_create2Bytes (n : Nat) (context : Context) (rt : Runtime) (v c s : Expr)
    {sv cv cv' vv : Value} {rt1 rt2 rt3 : Runtime} {salt value : Word} {code : List Byte}
    (hs : Expr.evalFuel n context rt s = .pure (sv, rt1)) (hsw : sv.expectWord = .ok salt)
    (hc : Expr.evalFuel n context rt1 c = .pure (cv, rt2))
    (hd : rt2.derefMemoryValue cv = .ok cv') (hcb : cv'.asBytes? = some code)
    (hv : Expr.evalFuel n context rt2 v = .pure (vv, rt3)) (hvw : vv.expectWord = .ok value) :
    Expr.evalFuel (n + 1) context rt (.create2Bytes v c s) =
      .request (.external (snapshotWorld context rt3.state)
          (.create (create2BytesRequest context code value salt)))
        (fun resp => .pure (Value.word (u256ToWord resp.address),
          { rt3 with state := adoptWorld resp.postWorld context rt3.state })) := by
  rw [Expr.evalFuel]
  simp only [hs, hsw, hc, hd, hv, hvw, ibind_pure, bind, pure, liftM, monadLift,
    MonadLift.monadLift, SolI.ofExcept, emitCreate2Bytes]
  simp only [ibind_done, hcb]
  rfl

/-- The request asks CREATE2. -/
theorem request_kind (context : Context) (code : List Byte) (value salt : Word) :
    (create2BytesRequest context code value salt).kind = .create2 := rfl

/-- The request's creator is the contract. -/
theorem request_creator (context : Context) (code : List Byte) (value salt : Word) :
    (create2BytesRequest context code value salt).creator = wordToAddress context.self := rfl

/-- The request's init code is the bytes of `code`. -/
theorem request_initCode (context : Context) (code : List Byte) (value salt : Word) :
    (create2BytesRequest context code value salt).initCode = bytesToByteArray code := rfl

/-- The request's salt is the salt word. -/
theorem request_salt (context : Context) (code : List Byte) (value salt : Word) :
    (create2BytesRequest context code value salt).salt = some (wordToU256 salt) := rfl

/-! ## The EVM's answer -/

/-- The 20-byte address of the low 160 bits of a word, big-endian. -/
def addressOfWord (w : Nat) : EthLib.Base.Address :=
  Vector.ofFn (fun i : Fin 20 => UInt8.ofNat (w / 256 ^ (19 - i.val)))

/-- EIP-1014's address of the creator, salt and init code, as a word: EthLib's
`create2Address` (the last 20 bytes of Keccak-256 of `0xff ++ creator ++ salt ++
keccak256(initCode)`). -/
def create2Word (creator salt : Nat) (initCode : ByteArray) : Nat :=
  EthLib.Base.bytesToNat (EthLib.Execution.Evm.create2Address (addressOfWord creator)
    (BitVec.ofNat 256 salt) initCode).toList

/-- **The environment answers a CREATE2 as the EVM does**: with the address 0 (the creation
failed: the init code reverted or ran out of gas, the address had code or a nonce, the value
exceeded the balance, the depth limit) or with EIP-1014's address. A premise about the open
world's answer, not about the hash. -/
def EvmCreate2 (req : CreateRequest) (resp : CreateResponse) : Prop :=
  req.kind = .create2 →
    u256ToWord resp.address = 0 ∨
      u256ToWord resp.address = create2Word (addressToWord req.creator)
        ((req.salt.map u256ToWord).getD 0) req.initCode

/-- Under an EVM answer, `create2Bytes` returns 0 or EIP-1014's address of the contract, the salt
and the bytes of the init code. -/
theorem answer_word (context : Context) (code : List Byte) (value salt : Word) (resp : CreateResponse)
    (h : EvmCreate2 (create2BytesRequest context code value salt) resp) :
    u256ToWord resp.address = 0 ∨
      u256ToWord resp.address = create2Word (addressToWord (wordToAddress context.self))
        (u256ToWord (wordToU256 salt)) (bytesToByteArray code) := by
  have h := h (request_kind context code value salt)
  rwa [request_initCode, request_salt, Option.map_some, Option.getD_some, request_creator] at h

/-- Not vacuous: the failed creation (the open world's default answer) is an EVM answer. -/
theorem evmCreate2_failed (req : CreateRequest) (w : OpenWorld) :
    EvmCreate2 req (Query.defaultAnswer (.external w (.create req))) :=
  fun _ => Or.inl rfl

/-- info: 'SolidCore.Refinement.CreateNode.eval_create2Bytes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms eval_create2Bytes

/-- info: 'SolidCore.Refinement.CreateNode.answer_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms answer_word

end SolidCore.Refinement.CreateNode
