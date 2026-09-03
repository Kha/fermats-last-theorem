import Mathlib
import P2M.Util
import P2M.Sol.S_HopfAlgebra_ker_counit_eq_sq_of_pow_eq_one_of_isUnit

set_option autoImplicit false

universe u v

theorem HopfAlgebra.ker_counit_eq_sq_of_pow_eq_one_of_isUnit
    {R : Type u} [CommRing R] {H : Type v} [CommRing H] [HopfAlgebra R H]
    (n : ℕ) (hn : IsUnit (n : R))
    (hH : ∀ (T : Type v) [CommRing T] [Algebra R T] (f : WithConv (H →ₐ[R] T)), f ^ n = 1) :
    RingHom.ker (Bialgebra.counitAlgHom R H) = RingHom.ker (Bialgebra.counitAlgHom R H) ^ 2 := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_ker_counit_eq_sq_of_pow_eq_one_of_isUnit.solution
