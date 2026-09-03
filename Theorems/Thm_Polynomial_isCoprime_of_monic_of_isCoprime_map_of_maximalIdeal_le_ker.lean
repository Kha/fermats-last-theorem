import Mathlib
import P2M.Util
import P2M.Sol.S_Polynomial_isCoprime_of_monic_of_isCoprime_map_of_maximalIdeal_le_ker
set_option autoImplicit false

open scoped Polynomial

theorem Polynomial.isCoprime_of_monic_of_isCoprime_map_of_maximalIdeal_le_ker
    {R k : Type*} [CommRing R] [IsLocalRing R] [Field k] (φ : R →+* k)
    (hφ : IsLocalRing.maximalIdeal R ≤ RingHom.ker φ)
    (f g : R[X]) (hf : f.Monic) (h : IsCoprime (f.map φ) (g.map φ)) :
    IsCoprime f g := by p2m_exact_reverting @_root_.P2MW.S_Polynomial_isCoprime_of_monic_of_isCoprime_map_of_maximalIdeal_le_ker.solution
