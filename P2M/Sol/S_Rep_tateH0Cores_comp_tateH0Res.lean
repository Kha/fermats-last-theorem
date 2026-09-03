import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_GroupCohomology_TateResCor
import P2M.Util
namespace P2MW.S_Rep_tateH0Cores_comp_tateH0Res

set_option autoImplicit false
universe u v w
open CategoryTheory Rep

theorem solution {k : Type u} {G : Type v} [CommRing k] [Group G] [Fintype G]
    (S : Subgroup G) [Fintype S] (A : Rep.{w} k G) :
    Rep.tateH0Cores S A ∘ₗ Rep.tateH0Res S A = (S.index : k) • LinearMap.id := by
  letI := Fintype.ofFinite (G ⧸ S)
  refine Submodule.linearMap_qext _ (LinearMap.ext fun a => ?_)
  simp only [LinearMap.comp_apply, Submodule.mkQ_apply, LinearMap.smul_apply, LinearMap.id_apply,
    Rep.tateH0Res_mk]
  rw [← Submodule.Quotient.mk_smul]
  refine congrArg Submodule.Quotient.mk (Subtype.ext ?_)
  rw [Representation.TateResCor.coe_cosetNormInvariants_apply, Submodule.coe_inclusion, Submodule.coe_smul,
    Representation.TateResCor.cosetNorm_apply, Finset.sum_congr rfl fun q _ => (Representation.mem_invariants _ _).1 a.2 q.out,
    Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, ← Subgroup.index_eq_card, Nat.cast_smul_eq_nsmul]
