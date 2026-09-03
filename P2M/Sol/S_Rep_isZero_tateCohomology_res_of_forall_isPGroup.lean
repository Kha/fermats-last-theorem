import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Theorems.Thm_Rep_isZero_tateCohomology_of_forall_sylow
import Theorems.Thm_Rep_isZero_tateCohomology_of_isPGroup_of_forall
import P2M.Util
namespace P2MW.S_Rep_isZero_tateCohomology_res_of_forall_isPGroup
attribute [-simp] Representation.TateResCor.cosetDecomp_apply Rep.coe_tateHneg1Res_apply Representation.TateResCor.coe_tateHneg1Cores_apply Representation.TateResCor.tateH0Res_mk Rep.coe_tateHneg1Cores_apply Rep.tateH0Res_mk Representation.TateResCor.coe_cosetNormInvariants_apply Rep.tateH0Cores_mk Representation.TateResCor.coinvariantsCores_mk Representation.TateResCor.coinvariantsTransfer_mk Representation.TateResCor.tateH0Cores_mk Representation.TateResCor.coe_tateHneg1Res_apply Rep.coe_tateδneg2_apply

set_option autoImplicit false
universe u
open CategoryTheory Rep
set_option maxHeartbeats 1600000

theorem solution {k G : Type u} [CommRing k] [Group G] [Fintype G]
    (A : Rep.{u} k G)
    (h : ∀ (p : ℕ) [Fact p.Prime] (P : Type u) [Group P] [Fintype P] (i : P →* G), Function.Injective i → IsPGroup p P →
      ∃ q : ℤ, CategoryTheory.Limits.IsZero ((Rep.res i A).tateCohomology q) ∧
        CategoryTheory.Limits.IsZero ((Rep.res i A).tateCohomology (q + 1)))
    (H : Type u) [Group H] [Fintype H] (f : H →* G) (hf : Function.Injective f) (q : ℤ) :
    CategoryTheory.Limits.IsZero ((Rep.res f A).tateCohomology q) := by
  classical

  refine Rep.isZero_tateCohomology_of_forall_sylow (Rep.res f A) q (fun p _ Q _ => ?_)
  show CategoryTheory.Limits.IsZero ((Rep.res (f.comp (Q : Subgroup H).subtype) A).tateCohomology q)
  refine Rep.isZero_tateCohomology_of_isPGroup_of_forall Q.isPGroup' (Rep.res (f.comp (Q : Subgroup H).subtype) A) ?_ q
  intro R _ _ g hg
  exact h p R ((f.comp (Q : Subgroup H).subtype).comp g) ((hf.comp (Q : Subgroup H).subtype_injective).comp hg)
    (IsPGroup.of_injective Q.isPGroup' g hg)
