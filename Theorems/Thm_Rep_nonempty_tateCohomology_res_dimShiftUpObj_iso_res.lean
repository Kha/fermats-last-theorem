import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_GroupCohomology_TateDimensionShift
import P2M.Util
import P2M.Sol.S_Rep_nonempty_tateCohomology_res_dimShiftUpObj_iso_res
attribute [-simp] Rep.coe_tateδneg2_apply Representation.TateResCor.cosetDecomp_apply Rep.coe_tateHneg1Res_apply Representation.TateResCor.coe_tateHneg1Cores_apply Representation.TateResCor.tateH0Res_mk Rep.coe_tateHneg1Cores_apply Rep.tateH0Res_mk Representation.TateResCor.coe_cosetNormInvariants_apply Rep.tateH0Cores_mk Representation.TateResCor.coinvariantsCores_mk Representation.TateResCor.coinvariantsTransfer_mk Representation.TateResCor.tateH0Cores_mk Representation.TateResCor.coe_tateHneg1Res_apply

set_option autoImplicit false
universe u
open CategoryTheory Rep
theorem Rep.nonempty_tateCohomology_res_dimShiftUpObj_iso_res {k G : Type u} [CommRing k] [Group G] [Fintype G]
    (S : Subgroup G) [Fintype S] (A : Rep.{u} k G) (q : ℤ) :
    Nonempty ((Rep.res S.subtype A.dimShiftUpObj).tateCohomology q ≅ (Rep.res S.subtype A).tateCohomology (q + 1)) := by p2m_exact_reverting @_root_.P2MW.S_Rep_nonempty_tateCohomology_res_dimShiftUpObj_iso_res.solution
