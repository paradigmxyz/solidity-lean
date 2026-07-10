import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

/-!
LIB-STORAGE-RETURN (#155) — public/external LIBRARY functions that RETURN a
storage reference or a `mapping(...)` type.

solc 0.8.35 ACCEPTS such library headers, symmetric with library functions that
TAKE storage/mapping parameters (already accepted, #90/#93). `checkHeader` in
`SolidCore/Solidity/TypeCheck.lean` formerly gated only the PARAM-side
storage/mapping/abi checks behind the `env.inLibrary` exemption while the
RETURN-side checks were UNCONDITIONAL, so the model over-rejected every library
function returning a storage ref or a mapping. The fix gates the four
return-side checks behind the SAME `env.inLibrary` exemption. Non-library
public/external functions returning storage/mapping STILL reject (both solc and
the model); internal functions are unaffected.

This witness imports the exact over-rejected library (a public `returns (S
storage)`, an external `returns (S storage)`, and a public
`returns (mapping storage)`) and pins that the whole unit is now ACCEPTED.

RUNTIME NOTE: the interpreter does not yet lower the *use* of a library
storage-return value (member access / index on the returned storage pointer);
that path fails with `TypeError.invalidType (Ty.user [.., "S"])` even for the
INTERNAL library case, so it is a SEPARATE unimplemented-runtime gap, distinct
from this acceptance over-reject. Real-EVM ground truth for the runtime
behavior (write/read through the returned storage/mapping ref => 42 / 99) lives
in `tests/forge-harness/lib-storage-return`.

`#eval`-confirmed booleans pinned with `#guard` (the project avoids
`native_decide`).
-/

namespace SolidCore
namespace Solidity
namespace SolcAstImport
namespace LibStorageReturn

def importedSourceName : String := "/private/tmp/claude-502/-Users-dan-Projects-solid-core-spine/a31e5b4d-dfd9-4ad6-82fd-d3eba32b9252/scratchpad/wt-lib-storage-return/tests/forge-harness/lib-storage-return/src/LibStorageReturn.sol"

def importedContractDecl0 : ContractDecl :=
{ kind := ContractKind.library
  name := "L"
  abstract := false
  bases := []
  items := [(ContractItem.structDecl
  { name := "S",
    fields := [{ name := "x", ty := Ty.uint 256 }] }), (ContractItem.structDecl
  { name := "D",
    fields := [{ name := "m", ty := Ty.mapping (Ty.uint 256) (Ty.uint 256) }] }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "refPublic",
    visibility := some Visibility.public_,
    mutability := StateMutability.view,
    params := [{ name := some "s", ty := Ty.user ({ segments := ["S"] }), location := some DataLocation.storage }],
    returns := [{ name := none, ty := Ty.user ({ segments := ["S"] }), location := some DataLocation.storage }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.ident "s"))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "refExternal",
    visibility := some Visibility.external_,
    mutability := StateMutability.view,
    params := [{ name := some "s", ty := Ty.user ({ segments := ["S"] }), location := some DataLocation.storage }],
    returns := [{ name := none, ty := Ty.user ({ segments := ["S"] }), location := some DataLocation.storage }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.ident "s"))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "mapPublic",
    visibility := some Visibility.public_,
    mutability := StateMutability.view,
    params := [{ name := some "d", ty := Ty.user ({ segments := ["D"] }), location := some DataLocation.storage }],
    returns := [{ name := none, ty := Ty.mapping (Ty.uint 256) (Ty.uint 256), location := some DataLocation.storage }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.member (Expr.ident "d") "m"))]) })] }

def importedContract : ContractDecl :=
  importedContractDecl0

def importedContracts : List ContractDecl :=
  [importedContractDecl0]

def importedSourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "^0.8.35", SourceItem.contract importedContractDecl0] }

def importedContractAccepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit importedSourceUnit)

end LibStorageReturn
end SolcAstImport
end Solidity
end SolidCore

namespace SolidCore
namespace Solidity
namespace Witness
namespace LibStorageReturn

/-- The library declaring public/external functions returning a storage ref and
a public function returning a `mapping storage` — over-rejected before #155 —
is ACCEPTED by the checker. -/
def libStorageReturnAccepted : Bool :=
  SolidCore.Solidity.SolcAstImport.LibStorageReturn.importedContractAccepted

#guard libStorageReturnAccepted

end LibStorageReturn
end Witness
end Solidity
end SolidCore
