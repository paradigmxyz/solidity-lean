import erc20_any.Statement
import erc20_any.Proof

namespace Certified.erc20_any.Final

theorem final : Statement := Certified.erc20_any.Proof.statement

end Certified.erc20_any.Final

#print axioms Certified.erc20_any.Final.final
