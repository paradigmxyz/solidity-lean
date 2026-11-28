import Verify.Obligation.Smt
import Verify.Obligation.Vc
import Verify.Obligation.Model

/-! The obligations `solar-verify --emit-lean` exports: the SMT-LIB fragment it writes with its
meaning (`Smt`), its scripts and obligations (`Vc`), and models of its answers (`Model`). An
exported module imports this one. -/
