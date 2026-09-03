import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_GroupCohomology_TateDimensionShift
import P2M.Util
import P2M.Sol.S_Rep_nonempty_res_indBot_iso
attribute [-simp] Representation.TateResCor.cosetDecomp_apply Rep.coe_tateHneg1Res_apply Representation.TateResCor.coe_tateHneg1Cores_apply Representation.TateResCor.tateH0Res_mk Rep.coe_tateHneg1Cores_apply Rep.tateH0Res_mk Representation.TateResCor.coe_cosetNormInvariants_apply Rep.tateH0Cores_mk Representation.TateResCor.coinvariantsCores_mk Representation.TateResCor.coinvariantsTransfer_mk Representation.TateResCor.tateH0Cores_mk Representation.TateResCor.coe_tateHneg1Res_apply

set_option autoImplicit false
universe u
open CategoryTheory Rep
theorem Rep.nonempty_res_indBot_iso {k G : Type u} [CommRing k] [Group G]
    (S : Subgroup G) (A : Rep.{u} k G) :
    Nonempty (Rep.res S.subtype A.indBot ≅ (Rep.trivial k S ((G ⧸ S) →₀ A)).indBot) := by p2m_exact_reverting @_root_.P2MW.S_Rep_nonempty_res_indBot_iso.solution
