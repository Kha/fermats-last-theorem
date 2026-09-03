import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_exists_charZero_point_specializes_of_natCast_mem_maximalIdeal_of_not_isNilpotent

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.exists_charZero_point_specializes_of_natCast_mem_maximalIdeal_of_not_isNilpotent
    {X : Scheme.{u}} (x : X) (n : ℕ)
    (hn : ((n : ℕ) : X.presheaf.stalk x) ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x))
    (hnil : ¬ IsNilpotent ((n : ℕ) : X.presheaf.stalk x)) :
    ∃ (K : Type u) (_ : Field K) (_ : CharZero K) (ξ : Spec (CommRingCat.of K) ⟶ X),
      ∀ z : Spec (CommRingCat.of K), ξ.base z ⤳ x := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_exists_charZero_point_specializes_of_natCast_mem_maximalIdeal_of_not_isNilpotent.solution
