import Mathlib
import P2M.Util
import P2M.Sol.S_HopfAlgebra_etale_of_pow_eq_one_of_isUnit_of_finite

set_option autoImplicit false

universe u v

theorem HopfAlgebra.etale_of_pow_eq_one_of_isUnit_of_finite
    {R : Type u} [CommRing R] {H : Type v} [CommRing H] [HopfAlgebra R H]
    [IsNoetherianRing R] [Module.Finite R H] [Module.Flat R H]
    (n : ℕ) (hn : IsUnit (n : R))
    (hH : ∀ (T : Type v) [CommRing T] [Algebra R T] (f : WithConv (H →ₐ[R] T)), f ^ n = 1) :
    Algebra.Etale R H := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_etale_of_pow_eq_one_of_isUnit_of_finite.solution
