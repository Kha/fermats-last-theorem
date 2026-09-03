import Mathlib
import P2M.Util
import P2M.Sol.S_PowerSeries_exists_monic_natDegree_eq_mul_of_map_eq_mul_X_pow

set_option autoImplicit false

open IsLocalRing PowerSeries

theorem PowerSeries.exists_monic_natDegree_eq_mul_of_map_eq_mul_X_pow
    {A : Type} [CommRing A] [IsLocalRing A] [IsAdicComplete (maximalIdeal A) A]
    {k : Type} [Field k] (θ : A →+* k) (hθ : ∀ a : A, θ a = 0 ↔ a ∈ maximalIdeal A)
    (g : PowerSeries A) (N : ℕ) (u : PowerSeries k) (hu : IsUnit u)
    (hg : PowerSeries.map θ g = u * PowerSeries.X ^ N) :
    ∃ (P : Polynomial A) (U : PowerSeries A),
      P.Monic ∧ P.natDegree = N ∧ (∀ i : ℕ, i < N → P.coeff i ∈ maximalIdeal A) ∧
      IsUnit U ∧ g = (P : PowerSeries A) * U := by p2m_exact_reverting @_root_.P2MW.S_PowerSeries_exists_monic_natDegree_eq_mul_of_map_eq_mul_X_pow.solution
