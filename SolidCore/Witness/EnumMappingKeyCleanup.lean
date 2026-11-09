import SolidCore.Solidity.Interpreter

namespace SolidCore.Solidity.Source

theorem coerceMappingKeyWordAs_propagates_cleanup_error
    (ty : Ty) (value : Value) (reason : RevertData)
    (h : value.forceAbiLazy = .error reason) :
    coerceMappingKeyWordAs ty value = .error reason := by
  unfold coerceMappingKeyWordAs
  rw [h]
  rfl

#print axioms coerceMappingKeyWordAs_propagates_cleanup_error

end SolidCore.Solidity.Source
