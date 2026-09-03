import Mathlib
import P2M.Util
import P2M.Sol.S_MvPowerSeries_exists_forall_coeff_mul_eq_pow_mul_and_residue_eq_coeff_mul_of_weightedInitialForm_ne_zero

set_option autoImplicit false

universe u v

theorem MvPowerSeries.exists_forall_coeff_mul_eq_pow_mul_and_residue_eq_coeff_mul_of_weightedInitialForm_ne_zero
    (σ : Type u) [Finite σ] (O : Type v) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (π : O) (hπ : Irreducible π) (m : ℕ) (hm : 1 ≤ m) (r c : ℕ)
    (ρ H : MvPowerSeries σ O) (ρbar : MvPolynomial σ (IsLocalRing.ResidueField O)) (hρbar : ρbar ≠ 0)
    (hρ : ∀ e : σ →₀ ℕ, m * e.degree ≤ r →
      ∃ a : O, MvPowerSeries.coeff e ρ = π ^ (r - m * e.degree) * a ∧
        IsLocalRing.residue O a = MvPolynomial.coeff e ρbar)
    (hρ' : ∀ e : σ →₀ ℕ, r < m * e.degree → MvPolynomial.coeff e ρbar = 0)
    (hHρ : ∀ e : σ →₀ ℕ, MvPowerSeries.coeff e (H * ρ) ∈ IsLocalRing.maximalIdeal O ^ (c - m * e.degree)) :
    ∃ Q : MvPolynomial σ (IsLocalRing.ResidueField O),
      (∀ e : σ →₀ ℕ, m * e.degree ≤ c →
        ∃ a : O, MvPowerSeries.coeff e (H * ρ) = π ^ (c - m * e.degree) * a ∧
          IsLocalRing.residue O a = MvPolynomial.coeff e (Q * ρbar)) ∧
      (∀ e : σ →₀ ℕ, c < m * e.degree → MvPolynomial.coeff e (Q * ρbar) = 0) := by p2m_exact_reverting @_root_.P2MW.S_MvPowerSeries_exists_forall_coeff_mul_eq_pow_mul_and_residue_eq_coeff_mul_of_weightedInitialForm_ne_zero.solution
