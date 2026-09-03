import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_affine_etale_cover_factor_of_forall_mem_range_of_etale

set_option autoImplicit false

universe v u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.exists_affine_etale_cover_factor_of_forall_mem_range_of_etale
    {T N : Scheme.{u}} [IsAffine T] (y : T ⟶ N)
    {ι : Type v} (X : ι → Scheme.{u}) (h : ∀ i, X i ⟶ N) [∀ i, Etale (h i)]
    (hsurj : ∀ z : N, ∃ i, z ∈ Set.range (h i)) :
    ∃ (n : ℕ) (i : Fin n → ι) (T' : Fin n → Scheme.{u}) (_ : ∀ j, IsAffine (T' j))
      (c : ∀ j, T' j ⟶ T) (_ : ∀ j, Etale (c j)) (w : ∀ j, T' j ⟶ X (i j)),
      (∀ t : T, ∃ j, t ∈ Set.range (c j)) ∧ ∀ j, w j ≫ h (i j) = c j ≫ y := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_affine_etale_cover_factor_of_forall_mem_range_of_etale.solution
