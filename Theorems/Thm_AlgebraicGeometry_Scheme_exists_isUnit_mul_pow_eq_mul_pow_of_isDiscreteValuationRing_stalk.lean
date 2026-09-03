import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_exists_isUnit_mul_pow_eq_mul_pow_of_isDiscreteValuationRing_stalk

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

theorem AlgebraicGeometry.Scheme.exists_isUnit_mul_pow_eq_mul_pow_of_isDiscreteValuationRing_stalk
    {X : Scheme.{0}} (t : Γ(X, ⊤)) (ξ : X)
    [IsDomain (X.presheaf.stalk ξ)] [IsDiscreteValuationRing (X.presheaf.stalk ξ)]
    (hmax : IsLocalRing.maximalIdeal (X.presheaf.stalk ξ) = Ideal.span {X.presheaf.Γgerm ξ t})
    (W : X.Opens) (hξ : ξ ∈ W) (u : Γ(X, W ⊓ X.basicOpen t)) (hu : IsUnit u) :
    ∃ (W' : X.Opens) (hW' : W' ≤ W) (_ : ξ ∈ W') (a b : ℕ) (v : Γ(X, W')), IsUnit v ∧
      X.presheaf.map (homOfLE (inf_le_inf_right (X.basicOpen t) hW')).op u *
          X.presheaf.map (homOfLE (le_top (a := W' ⊓ X.basicOpen t))).op t ^ a =
        X.presheaf.map (homOfLE (inf_le_left (a := W') (b := X.basicOpen t))).op v *
          X.presheaf.map (homOfLE (le_top (a := W' ⊓ X.basicOpen t))).op t ^ b := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_exists_isUnit_mul_pow_eq_mul_pow_of_isDiscreteValuationRing_stalk.solution
