import Verify.Lifecycle.CreationFrame
import Verify.Lifecycle.Route

/-!
# The four lifecycle examples deploy, by the generic creation frame

solar's init code for each example of tools/certify/examples/lifecycle (solar 0479b90a, -Ogas,
osaka), with its constructor arguments appended as ABI words (`initArgs`), deploys its runtime code
and storage: each theorem is `Creation.deploys_of_check`, one kernel evaluation of the generic
frame's `check`, with no instruction stepped for the contract. The runtime code `ImmutableCtor`
returns is solar's runtime code with the immutable word patched in at its reference (offset 45).

The negatives are `Creation.not_deploys_of_refutes`, again one kernel evaluation each: a wrong
argument, a missing storage slot, and the runtime code left without its immutable.
-/

open EthLib.Base EthLib.Execution EthLib.Execution.Evm EthLib.Execution.Evm.Logic
open SolidCore.Refinement Verify.Lifecycle.Creation

namespace Verify.Lifecycle.Deploy.Ctors

/-- Steps enough for each creation. -/
def fuel : Nat := 512
namespace NoArgCtor

/-- solar's init code, read big-endian. -/
def init : ByteArray := NatCode.ofNat 10715293703241361811014123202645468443465903242712748929245237465904604300910620647577406479277526680434458616347982938898322424376525867602081736515581 63
/-- solar's runtime code. -/
def runtime : ByteArray := NatCode.ofNat 28639634085878733390356966713628268571794318497599552101260479426727232901636059703017389291200274429 42
/-- The runtime code a creation installs. -/
def code : ByteArray := runtime
set_option maxRecDepth 100000 in
/-- **`NoArgCtor`'s init code, with the arguments [], deploys its runtime code and storage.** -/
theorem deploys : Deploys (initArgs init []) code [(0, 7)] :=
  deploys_of_check fuel (by decide +kernel)

end NoArgCtor
namespace ArgCtor

/-- solar's init code, read big-endian. -/
def init : ByteArray := NatCode.ofNat 6294415061350360205698280482399446761494930880808559032007119999485512629589562725775324390013852939536253287053120847898517190208942453309378146280625028486383186104503271145496288150173635729696834482329420052875848048213923766684462833973272326003306107452305397607206481231855635903732027821273128922337471747968479131270120622642286689147520130852736151079747998316730088144872180319394561153124078528015738003335557156761541920698498597429649406812405322398769097771112066127891238499953197049810659574911978675714048972054515 221
/-- solar's runtime code. -/
def runtime : ByteArray := NatCode.ofNat 11781665534480132229482883818773572482972322064764144386084373585745947345356356724213836115528763757635323525938496146090706587931364017915177685106771691667742707 68
/-- The runtime code a creation installs. -/
def code : ByteArray := runtime
set_option maxRecDepth 100000 in
/-- **`ArgCtor`'s init code, with the arguments [42, 48879], deploys its runtime code and storage.** -/
theorem deploys : Deploys (initArgs init [42, 48879]) code [(0, 42), (1, 48879)] :=
  deploys_of_check fuel (by decide +kernel)

end ArgCtor
namespace PairCtor

/-- solar's init code, read big-endian. -/
def init : ByteArray := NatCode.ofNat 27906327472947461407233641106563823520571736820589183382428787448531705190529517621487378107253664736475141553051603295184000103595816412936654164542523313504428892866427945962650479544453803444867226816023744181330525789318850857016386565694948637511603036300053097342618577202198211410459112223743798369114372854531473810682077774547481978758438586103522859902010679283 154
/-- solar's runtime code. -/
def runtime : ByteArray := NatCode.ofNat 41857006246702727319087453598820390478671036200549347915890176230053171284533454133906445021468681725530285210345330296491421237469357747105635000307 62
/-- The runtime code a creation installs. -/
def code : ByteArray := runtime
set_option maxRecDepth 100000 in
/-- **`PairCtor`'s init code, with the arguments [42, 48879], deploys its runtime code and storage.** -/
theorem deploys : Deploys (initArgs init [42, 48879]) code [(0, 42), (1, 48921)] :=
  deploys_of_check fuel (by decide +kernel)

end PairCtor
namespace ImmutableCtor

/-- solar's init code, read big-endian. -/
def init : ByteArray := NatCode.ofNat 49366025695614005449881583999679351673965258260670546813828747010791289063152781984271361150165825784563553453520591257607532794934640091084952401022846332091419047698080899500384181730112649045259987802233513087343585773851763844264094882211667581203083709525670522878799387538151779642026779087982284494190912329929684590968572817263603309641576433902533318877676147400315381569093047007167318930053465282261257990409036965401512635782946803 184
/-- solar's runtime code. -/
def runtime : ByteArray := NatCode.ofNat 73954713172230683768847000394358160258572216562488243577265112580901765046640210907377197726227815204963788898024457746917637956324574262736192342673878701280198516939889491566945348079329698415133594229113048288783785971 92
/-- The runtime code a creation installs: solar's, with the immutable at offset 45. -/
def code : ByteArray := patchWord runtime 45 1000
set_option maxRecDepth 100000 in
/-- **`ImmutableCtor`'s init code, with the arguments [1000], deploys its runtime code and storage.** -/
theorem deploys : Deploys (initArgs init [1000]) code [(0, 1001)] :=
  deploys_of_check fuel (by decide +kernel)

end ImmutableCtor
/-! ## Kernel negatives -/

set_option maxRecDepth 100000 in
/-- A wrong argument: `ArgCtor` created with 41 does not leave slot 0 holding 42. -/
theorem argCtor_wrong_arg :
    ¬ Deploys (initArgs ArgCtor.init [41, 0xbeef]) ArgCtor.code [(0, 42), (1, 48879)] :=
  not_deploys_of_refutes fuel (by decide +kernel)

set_option maxRecDepth 100000 in
/-- A missing slot: `ArgCtor`'s creation leaves slot 1 written, so storage without it is refuted. -/
theorem argCtor_missing_slot :
    ¬ Deploys (initArgs ArgCtor.init [42, 0xbeef]) ArgCtor.code [(0, 42)] :=
  not_deploys_of_refutes fuel (by decide +kernel)

set_option maxRecDepth 100000 in
/-- A missing slot: `PairCtor`'s second slot dropped. -/
theorem pairCtor_missing_slot :
    ¬ Deploys (initArgs PairCtor.init [42, 0xbeef]) PairCtor.code [(0, 42)] :=
  not_deploys_of_refutes fuel (by decide +kernel)

set_option maxRecDepth 100000 in
/-- An unpatched immutable: `ImmutableCtor` does not install solar's runtime code as compiled. -/
theorem immutableCtor_unpatched :
    ¬ Deploys (initArgs ImmutableCtor.init [1000]) ImmutableCtor.runtime [(0, 1001)] :=
  not_deploys_of_refutes fuel (by decide +kernel)

set_option maxRecDepth 100000 in
/-- A wrong argument for the immutable: created with 999, the patched word is not 1000. -/
theorem immutableCtor_wrong_arg :
    ¬ Deploys (initArgs ImmutableCtor.init [999]) ImmutableCtor.code [(0, 1000)] :=
  not_deploys_of_refutes fuel (by decide +kernel)

/-- info: 'Verify.Lifecycle.Deploy.Ctors.ImmutableCtor.deploys' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ImmutableCtor.deploys

/-- info: 'Verify.Lifecycle.Deploy.Ctors.immutableCtor_unpatched' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms immutableCtor_unpatched

end Verify.Lifecycle.Deploy.Ctors
