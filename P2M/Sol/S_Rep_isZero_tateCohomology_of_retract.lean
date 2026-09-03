import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_GroupCohomology_TateSeam
import Definitions.Def_GroupCohomology_TateShiftMaps
import Theorems.Thm_Rep_tateMap_id
import Theorems.Thm_Rep_tateMap_comp
import P2M.Util
namespace P2MW.S_Rep_isZero_tateCohomology_of_retract

set_option autoImplicit false
universe u
open CategoryTheory Rep

theorem solution {k G : Type u} [CommRing k] [Group G] [Fintype G]
    {A B : Rep.{u} k G} (i : A ⟶ B) (r : B ⟶ A) (hir : i ≫ r = 𝟙 A) (q : ℤ)
    (hB : CategoryTheory.Limits.IsZero (B.tateCohomology q)) :
    CategoryTheory.Limits.IsZero (A.tateCohomology q) := by
  rw [Limits.IsZero.iff_id_eq_zero, ← Rep.tateMap_id, ← hir, Rep.tateMap_comp, hB.eq_of_tgt (Rep.tateMap i q) 0,
    Limits.zero_comp]
