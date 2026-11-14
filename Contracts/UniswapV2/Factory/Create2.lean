import EthLib.Execution.Evm.Call.ContractAddress
import EthLib.Base.Proofs.U256

/-!
# CREATE2 addresses under a modelled hash

The address of the pair `UniswapV2Factory.createPair` deploys is EIP-1014's: the last 20 bytes of the
hash of `0xff ++ factory ++ salt ++ hash(initCode)`, with `salt = hash(token0 ++ token1)` (the 40
bytes of `abi.encodePacked(token0, token1)`). EthLib computes it with its Keccak-256
(`EthLib.Execution.Evm.create2Address`), which `create2Address_eq` restates over any hash `H`.

Keccak-256 is modelled as hevm and Certora do: an uninterpreted function with named assumptions.
`KeccakModel H xs` says `H` has no collision on the finite list `xs` of inputs a statement uses, in
the whole digest and in its last 20 bytes (the address). It is stated over a finite list on purpose:
injectivity on every input, or on every input of one length above 32 bytes, is refuted by counting
for Keccak-256 itself, so a statement assuming it of the real hash would hold vacuously. Over a
finite list the premise is consistent with the real hash (it is what "no collision among the hashes
this run computes" means) and stays a premise: nothing here proves it of Keccak-256.

Proved: two pairs created by the same factory from the same init code at the same address were
created for the same ordered tokens (`pair_inj`), and the address is a function of the sorted tokens
(`pairAddr_comm`), so creating (A, B) and (B, A) name one pair.
-/

namespace Contracts.UniswapV2.Factory.Create2

open EthLib.Base EthLib.Execution.Evm

/-- A 32-byte hash function. -/
abbrev Hash := ByteArray → Vector UInt8 32

/-- EIP-1014's address under a hash `H`. -/
def create2AddrH (H : Hash) (sender : Address) (salt : U256) (init : ByteArray) : Address :=
  addressOfHash (H (create2Preimage sender salt (H init)))

/-- EthLib's CREATE2 address is the model's at EthLib's Keccak-256. -/
theorem create2Address_eq (sender : Address) (salt : U256) (init : ByteArray) :
    create2Address sender salt init =
      create2AddrH EthLib.Cryptography.Hash.Keccak.keccak256 sender salt init := rfl

/-- **The hash model** (one named premise): no collision of `H` on the inputs `xs`, in the digest
and in its address bytes. -/
structure KeccakModel (H : Hash) (xs : List ByteArray) : Prop where
  inj : ∀ a ∈ xs, ∀ b ∈ xs, H a = H b → a = b
  addrInj : ∀ a ∈ xs, ∀ b ∈ xs, addressOfHash (H a) = addressOfHash (H b) → a = b

/-- `abi.encodePacked(token0, token1)`: the 40 bytes of two addresses. -/
def packed (t0 t1 : Address) : ByteArray := ⟨t0.toArray⟩ ++ ⟨t1.toArray⟩

/-- The salt of `createPair`: the hash of the packed tokens, as a word. -/
def saltOf (H : Hash) (t0 t1 : Address) : U256 := U256.fromBeBytes (H (packed t0 t1))

/-- The pair's address: CREATE2 from the factory with the pair's salt and init code. -/
def pairAddr (H : Hash) (factory : Address) (init : ByteArray) (t0 t1 : Address) : Address :=
  create2AddrH H factory (saltOf H t0 t1) init

/-- The inputs whose hashes `createPair` of `(t0, t1)` computes: the packed tokens and the
CREATE2 preimage (the init code's hash is shared by every pair). -/
def inputs (H : Hash) (factory : Address) (init : ByteArray) (t0 t1 : Address) : List ByteArray :=
  [packed t0 t1, create2Preimage factory (saltOf H t0 t1) (H init)]

theorem toList_data_mk (v : Array UInt8) : (ByteArray.mk v).data.toList = v.toList := rfl

/-- The list of bytes of a CREATE2 preimage. -/
theorem preimage_toList (sender : Address) (salt : U256) (h : Vector UInt8 32) :
    (create2Preimage sender salt h).data.toList =
      [0xff] ++ sender.toList ++ (U256.toBeBytes salt).toList ++ h.toList := by
  simp [create2Preimage, Vector.toList]

/-- The preimage determines the salt. -/
theorem salt_of_preimage {sender : Address} {s1 s2 : U256} {h : Vector UInt8 32}
    (he : create2Preimage sender s1 h = create2Preimage sender s2 h) : s1 = s2 := by
  have hl := congrArg (fun b : ByteArray => b.data.toList) he
  simp only [preimage_toList] at hl
  have h1 : (U256.toBeBytes s1).toList = (U256.toBeBytes s2).toList := by
    have := List.append_cancel_right hl
    simpa [List.append_assoc] using this
  exact U256.toBeBytes_inj (Vector.toList_inj.mp h1)

/-- The packed tokens determine the tokens. -/
theorem tokens_of_packed {a0 a1 b0 b1 : Address} (he : packed a0 a1 = packed b0 b1) :
    a0 = b0 ∧ a1 = b1 := by
  have hl := congrArg (fun b : ByteArray => b.data.toList) he
  simp only [packed, ByteArray.toList_data_append] at hl
  have hlen : a0.toArray.toList.length = b0.toArray.toList.length := by simp
  obtain ⟨h0, h1⟩ := List.append_inj hl hlen
  exact ⟨Vector.toArray_inj.mp (Array.toList_inj.mp h0), Vector.toArray_inj.mp (Array.toList_inj.mp h1)⟩

/-- **One address, one pair**: under the hash model on the inputs of both creations, two pairs the
same factory creates from the same init code at the same address have the same ordered tokens. -/
theorem pair_inj {H : Hash} {factory : Address} {init : ByteArray} {a0 a1 b0 b1 : Address}
    (hm : KeccakModel H (inputs H factory init a0 a1 ++ inputs H factory init b0 b1))
    (he : pairAddr H factory init a0 a1 = pairAddr H factory init b0 b1) : a0 = b0 ∧ a1 = b1 := by
  have hpre := hm.addrInj _ (by simp [inputs]) _ (by simp [inputs]) he
  have hs := salt_of_preimage hpre
  have hh : H (packed a0 a1) = H (packed b0 b1) := by
    have := congrArg U256.toBeBytes hs
    simpa [saltOf, U256.toBeBytes_fromBeBytes] using this
  exact tokens_of_packed (hm.inj _ (by simp [inputs]) _ (by simp [inputs]) hh)

/-- The ordered tokens of `createPair(tokenA, tokenB)`: the smaller address first. -/
def sortTokens (a b : Address) : Address × Address :=
  if a.toU256 < b.toU256 then (a, b) else (b, a)

/-- `createPair(A, B)` and `createPair(B, A)` derive one address when `A ≠ B`. -/
theorem pairAddr_comm (H : Hash) (factory : Address) (init : ByteArray) {a b : Address}
    (hab : a.toU256 ≠ b.toU256) :
    pairAddr H factory init (sortTokens a b).1 (sortTokens a b).2 =
      pairAddr H factory init (sortTokens b a).1 (sortTokens b a).2 := by
  unfold sortTokens
  have hne : a.toU256.toNat ≠ b.toU256.toNat := fun h => hab (BitVec.eq_of_toNat_eq h)
  by_cases h1 : a.toU256 < b.toU256
  · have h2 : ¬ b.toU256 < a.toU256 := by
      rw [BitVec.lt_def] at h1 ⊢
      omega
    simp [h1, h2]
  · have h2 : b.toU256 < a.toU256 := by
      rw [BitVec.lt_def] at h1 ⊢
      omega
    simp [h1, h2]

/-- info: 'Contracts.UniswapV2.Factory.Create2.pair_inj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pair_inj

end Contracts.UniswapV2.Factory.Create2
