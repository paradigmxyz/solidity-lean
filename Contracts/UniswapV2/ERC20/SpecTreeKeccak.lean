import SolidCore.Solidity.Interpreter
import SolidCore.Refinement.KernelRfl

/-!
# The constructor's Keccak-256 hashes of UniswapV2ERC20, by table

UniswapV2ERC20's constructor sets `DOMAIN_SEPARATOR` to the EIP-712 domain hash: Keccak-256 of the
domain type string, of the name `Uniswap V2`, of the version `1`, and of the ABI encoding of the three
with the chain ID (0 in SolidCore's closed deployment context) and the contract's address
(`selfAddress`). The kernel's evaluation of one hash costs about 400 MB, so each is checked once,
in its own declaration (`kernel_rfl`), and `keccakWord_eq` replaces SolidCore's `keccakWord` by a
table of the four, which a `kernel_rfl` of the deployment takes with `using`, as the cores take
`selector_eq`. Every other input is hashed as before.
-/

namespace SolidCore.Spec.UniswapV2.ERC20.Keccak

open SolidCore.Solidity SolidCore.Solidity.Source

/-- The UTF-8 bytes of a string. -/
def sb (s : String) : List Nat := s.toUTF8.toList.map (·.toNat)

/-- The EIP-712 domain type string. -/
def domainType : List Nat :=
  sb "EIP712Domain(string name,string version,uint256 chainId,address verifyingContract)"
def nameBytes : List Nat := sb "Uniswap V2"
def versionBytes : List Nat := sb "1"

abbrev kDomainType : Nat := 63076024560530113402979550242307453568063438748328787417531900361828837441551
abbrev kName : Nat := 86753177656789946143617852270382413483605072673293953774383968070347263481656
abbrev kVersion : Nat := 90743482286830539503240959006302832933333810038750515972785732718729991261126

/-- The ABI encoding the constructor hashes: the three hashes, the chain ID 0 and the address. -/
def domainBytes : List Nat :=
  storageWordBytes kDomainType ++ storageWordBytes kName ++ storageWordBytes kVersion ++
    storageWordBytes 0 ++ storageWordBytes 0x1000

abbrev kDomain : Nat := 78390027508550153555773896992835392567232765649225488394068785439274740276969

def hDomainType : Nat := keccakWord domainType
kernel_rfl hDomainType_eq hDomainType kDomainType
def hName : Nat := keccakWord nameBytes
kernel_rfl hName_eq hName kName
def hVersion : Nat := keccakWord versionBytes
kernel_rfl hVersion_eq hVersion kVersion
def hDomain : Nat := keccakWord domainBytes
kernel_rfl hDomain_eq hDomain kDomain

/-- `keccakWord`, with the constructor's four hashes by table. -/
def keccakTable (bs : List Nat) : Nat :=
  if bs = domainType then kDomainType
  else if bs = nameBytes then kName
  else if bs = versionBytes then kVersion
  else if bs = domainBytes then kDomain
  else keccakWord bs

theorem keccakWord_eq : keccakWord = keccakTable := by
  funext bs
  unfold keccakTable
  by_cases h0 : bs = domainType
  · rw [if_pos h0, h0]; exact hDomainType_eq
  rw [if_neg h0]
  by_cases h1 : bs = nameBytes
  · rw [if_pos h1, h1]; exact hName_eq
  rw [if_neg h1]
  by_cases h2 : bs = versionBytes
  · rw [if_pos h2, h2]; exact hVersion_eq
  rw [if_neg h2]
  by_cases h3 : bs = domainBytes
  · rw [if_pos h3, h3]; exact hDomain_eq
  rw [if_neg h3]

/-- info: 'SolidCore.Spec.UniswapV2.ERC20.Keccak.keccakWord_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms keccakWord_eq

end SolidCore.Spec.UniswapV2.ERC20.Keccak
