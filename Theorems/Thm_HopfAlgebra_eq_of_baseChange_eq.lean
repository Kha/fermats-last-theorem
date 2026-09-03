import Mathlib
import P2M.Util
import P2M.Sol.S_HopfAlgebra_eq_of_baseChange_eq

universe u v

theorem HopfAlgebra.eq_of_baseChange_eq
    {R : Type u} [CommRing R] [IsDomain R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {H : Type v} [CommRing H] [HopfAlgebra R H]
    {H' : Type v} [CommRing H'] [HopfAlgebra R H'] [Module.Flat R H']
    (φ ψ : H →ₐc[R] H')
    (h : (φ : H →ₐ[R] H').toLinearMap.baseChange K = (ψ : H →ₐ[R] H').toLinearMap.baseChange K) :
    φ = ψ := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_eq_of_baseChange_eq.solution
