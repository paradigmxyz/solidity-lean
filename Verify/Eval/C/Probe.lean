import Verify.Eval.C.Rules
open EthLib.Base EthLib.Execution EthLib.Execution.Evm EthLib.Execution.Evm.Logic
set_option maxRecDepth 100000
example (msg : Message .fusaka)
    (h : msg.value ≠ 0 ∨ loadWord msg.data 0 32 >>> 224 ≠ 0xb3de648b ∨ msg.data.size < 36)
    (h1 : msg.value = 0) (h2 : 0xb3de648b - loadWord msg.data 0 32 >>> 224 = 0)
    (h3 : (if BitVec.ofNat 256 msg.data.size < 36 then 1 else 0 : U256) = 0) : False := by
  grind
example (msg : Message .fusaka)
    (h : msg.value ≠ 0 ∨ loadWord msg.data 0 32 >>> 224 ≠ 0xb3de648b ∨ msg.data.size < 36)
    (h1 : msg.value = 0) (h2 : 0xb3de648b - loadWord msg.data 0 32 >>> 224 = 0)
    (h3 : (if BitVec.ofNat 256 msg.data.size < 36 then 1 else 0 : U256) = 0) : False := by
  bv_omega
