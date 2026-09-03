import Mathlib
import Theorems.Thm_AlgebraicGeometry_dense_setOf_exists_section_of_isAlgClosed
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_Scheme_Hom_eq_of_forall_comp_eq_of_dense_of_isAlgClosed

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem solution
    (k : Type u) [Field k] [IsAlgClosed k] {X Y S : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    [IsReduced X] [LocallyOfFiniteType f]
    (F G : X ⟶ Y) (i : Y ⟶ S) [IsSeparated i] (hFG : F ≫ i = G ≫ i)
    (U : X.Opens) (hU : Dense (U : Set ↥X))
    (h : ∀ y : Spec (CommRingCat.of k) ⟶ X, y ≫ f = 𝟙 _ → y.base (IsLocalRing.closedPoint k) ∈ U →
      y ≫ F = y ≫ G) :
    F = G := by
  have hP := AlgebraicGeometry.dense_setOf_exists_section_of_isAlgClosed f
  have hD : Dense ((U : Set ↥X) ∩ {x : ↥X | ∃ s : Spec (.of k) ⟶ X, s ≫ f = 𝟙 _ ∧ s (IsLocalRing.closedPoint k) = x}) :=
    hU.inter_of_isOpen_left hP U.isOpen
  suffices IsDominant (equalizer.ι F G) from
    ext_of_isDominant_of_isSeparated i hFG (equalizer.ι F G) (equalizer.condition _ _)
  refine ⟨.mono (fun x hx => ?_) hD⟩
  obtain ⟨hxU, y, hy, hyx⟩ := hx
  have hyU : y.base (IsLocalRing.closedPoint k) ∈ U := by rw [← hyx] at hxU; exact hxU
  refine ⟨equalizer.lift y (h y hy hyU) (IsLocalRing.closedPoint k), ?_⟩
  rw [← Scheme.Hom.comp_apply, equalizer.lift_ι]
  exact hyx
