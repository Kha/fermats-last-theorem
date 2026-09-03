import Mathlib
import P2M.Util
import P2M.Sol.S_MvPowerSeries_exists_apply_eq_mul_pow_mul_add_of_mem_span_X_pow_of_apply_X_eq_mul

set_option autoImplicit false

open IsLocalRing

theorem MvPowerSeries.exists_apply_eq_mul_pow_mul_add_of_mem_span_X_pow_of_apply_X_eq_mul
    (W : Type) [CommRing W] (M : Type) [CommRing M] [IsLocalRing M]
    (Φ : MvPowerSeries (Fin 2) W →+* M) (ρ : W →+* M)
    (hC : ∀ w : W, Φ (MvPowerSeries.C w) = ρ w)
    (v α β : M) (p₀ p₁ : W)
    (hX0 : Φ (MvPowerSeries.X 0) = v * α) (hX1 : Φ (MvPowerSeries.X 1) = v * β)
    (hv : v ∈ maximalIdeal M)
    (hα : α - ρ p₀ ∈ maximalIdeal M) (hβ : β - ρ p₁ ∈ maximalIdeal M)
    (d : ℕ) (g : MvPowerSeries (Fin 2) W)
    (hg : g ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}) ^ d) :
    ∃ r ∈ maximalIdeal M,
      Φ g = v ^ d * (ρ (∑ i ∈ Finset.range (d + 1),
        MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) i + Finsupp.single (1 : Fin 2) (d - i)) g * p₀ ^ i * p₁ ^ (d - i)) + r) := by p2m_exact_reverting @_root_.P2MW.S_MvPowerSeries_exists_apply_eq_mul_pow_mul_add_of_mem_span_X_pow_of_apply_X_eq_mul.solution
