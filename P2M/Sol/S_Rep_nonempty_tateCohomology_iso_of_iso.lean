import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import P2M.Util
namespace P2MW.S_Rep_nonempty_tateCohomology_iso_of_iso

set_option autoImplicit false
universe u
open CategoryTheory Rep

theorem solution {k G : Type u} [CommRing k] [Group G] [Fintype G]
    {A B : Rep.{u} k G} (e : A ≅ B) (q : ℤ) : Nonempty (A.tateCohomology q ≅ B.tateCohomology q) := by
  rcases q with (_ | n) | (_ | n)
  · refine ⟨(LinearEquiv.ofLinear (Rep.tateH0Map e.hom) (Rep.tateH0Map e.inv) ?_ ?_).toModuleIso⟩
    · rw [← Rep.tateH0Map_comp, e.inv_hom_id, Rep.tateH0Map_id]
    · rw [← Rep.tateH0Map_comp, e.hom_inv_id, Rep.tateH0Map_id]
  · exact ⟨(groupCohomology.functor k G (n + 1)).mapIso e⟩
  · refine ⟨(LinearEquiv.ofLinear (Rep.tateHneg1Map e.hom) (Rep.tateHneg1Map e.inv) ?_ ?_).toModuleIso⟩
    · rw [← Rep.tateHneg1Map_comp, e.inv_hom_id, Rep.tateHneg1Map_id]
    · rw [← Rep.tateHneg1Map_comp, e.hom_inv_id, Rep.tateHneg1Map_id]
  · exact ⟨(groupHomology.functor k G (n + 1)).mapIso e⟩
