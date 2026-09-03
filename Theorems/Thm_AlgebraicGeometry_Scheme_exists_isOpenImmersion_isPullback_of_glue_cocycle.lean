import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_exists_isOpenImmersion_isPullback_of_glue_cocycle

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.exists_isOpenImmersion_isPullback_of_glue_cocycle
    {S X U : Scheme.{u}} (f : X ⟶ S) (j : U ⟶ X) [IsOpenImmersion j]
    {ι : Type u} (t : ι → ι → (U ≅ U))
    (ht_over : ∀ i k, (t i k).hom ≫ j ≫ f = j ≫ f)
    (ht_refl : ∀ i, t i i = Iso.refl U)
    (ht_trans : ∀ i k l, (t i k).hom ≫ (t k l).hom = (t i l).hom) :
    ∃ (N : Scheme.{u}) (gN : N ⟶ S) (e : ι → (X ⟶ N)),
      (∀ i, IsOpenImmersion (e i)) ∧
      (∀ i, e i ≫ gN = f) ∧
      (⋃ i, Set.range (e i).base) = Set.univ ∧
      (∀ i k, i ≠ k → IsPullback j ((t i k).hom ≫ j) (e i) (e k)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_exists_isOpenImmersion_isPullback_of_glue_cocycle.solution
