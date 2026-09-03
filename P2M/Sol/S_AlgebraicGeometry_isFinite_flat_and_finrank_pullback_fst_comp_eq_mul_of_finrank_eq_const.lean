import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_finrank_comp_of_finrank_eq_const
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_isFinite_flat_and_finrank_pullback_fst_comp_eq_mul_of_finrank_eq_const

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem solution
    {X Y Z : Scheme.{u}} (g : X ⟶ Z) (h : Y ⟶ Z)
    [IsFinite g] [Flat g] [LocallyOfFinitePresentation g] [IsFinite h] [Flat h] [LocallyOfFinitePresentation h]
    (m n : ℕ) (hg : ∀ z : Z, g.finrank z = m) (hh : ∀ z : Z, h.finrank z = n) :
    IsFinite (pullback.fst g h ≫ g) ∧ Flat (pullback.fst g h ≫ g) ∧ LocallyOfFinitePresentation (pullback.fst g h ≫ g) ∧
      ∀ z : Z, (pullback.fst g h ≫ g).finrank z = m * n := by
  refine ⟨inferInstance, inferInstance, inferInstance, fun z => ?_⟩
  have hc : ∀ x : X, (pullback.fst g h).finrank x = n := fun x => by
    rw [Scheme.Hom.finrank_pullback_fst]; exact hh _
  rw [Scheme.Hom.finrank_comp_of_finrank_eq_const (pullback.fst g h) g n hc z, hg z, mul_comm]
