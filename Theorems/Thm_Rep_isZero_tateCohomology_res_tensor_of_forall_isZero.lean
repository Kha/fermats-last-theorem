import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import P2M.Util
import P2M.Sol.S_Rep_isZero_tateCohomology_res_tensor_of_forall_isZero
attribute [-simp] Rep.coe_tateδneg2_apply Representation.TateResCor.cosetDecomp_apply Rep.coe_tateHneg1Res_apply Representation.TateResCor.coe_tateHneg1Cores_apply Representation.TateResCor.tateH0Res_mk Rep.coe_tateHneg1Cores_apply Rep.tateH0Res_mk Representation.TateResCor.coe_cosetNormInvariants_apply Rep.tateH0Cores_mk Representation.TateResCor.coinvariantsCores_mk Representation.TateResCor.coinvariantsTransfer_mk Representation.TateResCor.tateH0Cores_mk Representation.TateResCor.coe_tateHneg1Res_apply

set_option autoImplicit false
universe u
open CategoryTheory Rep MonoidalCategory
theorem Rep.isZero_tateCohomology_res_tensor_of_forall_isZero {G : Type} [Group G] [Fintype G] (B : Rep ℤ G)
    (V : Type) [AddCommGroup V] [Module.Free ℤ V] (ρ : Representation ℤ G V)
    (hB : ∀ (S : Subgroup G) [Fintype S] (q : ℤ), CategoryTheory.Limits.IsZero ((Rep.res S.subtype B).tateCohomology q))
    (S : Subgroup G) [Fintype S] (q : ℤ) :
    CategoryTheory.Limits.IsZero ((Rep.res S.subtype (B ⊗ Rep.of ρ)).tateCohomology q) := by p2m_exact_reverting @_root_.P2MW.S_Rep_isZero_tateCohomology_res_tensor_of_forall_isZero.solution
