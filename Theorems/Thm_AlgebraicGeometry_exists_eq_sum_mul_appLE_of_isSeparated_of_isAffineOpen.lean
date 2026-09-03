import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_eq_sum_mul_appLE_of_isSeparated_of_isAffineOpen

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

universe u

theorem AlgebraicGeometry.exists_eq_sum_mul_appLE_of_isSeparated_of_isAffineOpen
    {R : Type u} [CommRing R] {X Y : Scheme.{u}} (q : Y ⟶ Spec (CommRingCat.of R)) [IsSeparated q]
    (g : X ⟶ Y) (U : X.Opens) (hU : IsAffineOpen U) (V : Y.Opens) (hV : IsAffineOpen V)
    (t : Γ(X, U ⊓ g ⁻¹ᵁ V)) :
    ∃ (n : ℕ) (a : Fin n → Γ(X, U)) (b : Fin n → Γ(Y, V)),
      t = ∑ k, (X.presheaf.map (homOfLE (inf_le_left : U ⊓ g ⁻¹ᵁ V ≤ U)).op).hom (a k) *
            (g.appLE V (U ⊓ g ⁻¹ᵁ V) inf_le_right).hom (b k) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_eq_sum_mul_appLE_of_isSeparated_of_isAffineOpen.solution
