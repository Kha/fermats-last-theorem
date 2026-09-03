import Definitions.Def_AutomorphicForm_SatakeCombinationCoeff
import P2M.Util
import P2M.Sol.S_AutomorphicForm_SatakeCombination_mul_sum_slotCoeff_div_pow_mul_ite_apply_T_add_T_inv_pow_eq_ite_sqrt_mul_pow_mul_zpow_neg

set_option autoImplicit false

open IsDedekindDomain NumberField

theorem AutomorphicForm.SatakeCombination.mul_sum_slotCoeff_div_pow_mul_ite_apply_T_add_T_inv_pow_eq_ite_sqrt_mul_pow_mul_zpow_neg
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (ws : ∀ v : HeightOneSpectrum (𝓞 K), v.Extension (𝓞 L))
    (v : HeightOneSpectrum (𝓞 K)) (k j : ℕ)

    (hf : 0 < AutomorphicForm.SatakeCombination.slotDeg K L ws v)
    (Nw : ℕ) (hNw : Ideal.absNorm (ws v).1.asIdeal = Nw)
    (hNwf : Nw = Ideal.absNorm v.asIdeal ^ AutomorphicForm.SatakeCombination.slotDeg K L ws v)

    (ζ s x : ℂ) (hζ : ζ ≠ 0) (hs : s ^ 2 = ζ)
    (hx : x ^ AutomorphicForm.SatakeCombination.slotDeg K L ws v = ζ)
    (m₁ m₂ : ℤ) :
    (x * (Ideal.absNorm v.asIdeal : ℂ)) ^ m₂ *
        ∑ r ∈ (AutomorphicForm.SatakeCombination.slotWord K L ws v k j).support,
          AutomorphicForm.SatakeCombination.slotCoeff K L ws v k j r /
              (Ideal.absNorm v.asIdeal : ℂ) ^ (r 1) *
            (if m₁ + m₂ = ((r 0 : ℕ) : ℤ) + 2 * ((r 1 : ℕ) : ℤ) then
              ((LaurentPolynomial.T 1 + LaurentPolynomial.T (-1)) ^ (r 0) : LaurentPolynomial ℂ).coeff (m₁ - m₂)
            else 0) =
      if (AutomorphicForm.SatakeCombination.slotDeg K L ws v : ℤ) ∣ m₂ ∧
          m₁ + m₂ = (AutomorphicForm.SatakeCombination.slotDeg K L ws v : ℤ) * ((k : ℤ) + 2 * (j : ℤ)) then
        ((Real.sqrt (Nw : ℝ) : ℂ) * s) ^ k * ζ ^ j *
            ((LaurentPolynomial.T 1 + LaurentPolynomial.T (-1)) ^ k : LaurentPolynomial ℂ).coeff
              ((m₁ - m₂) / (AutomorphicForm.SatakeCombination.slotDeg K L ws v : ℤ)) *
          ((Real.sqrt (Nw : ℝ) : ℂ) * s) ^ (-((m₁ - m₂) / (AutomorphicForm.SatakeCombination.slotDeg K L ws v : ℤ)))
      else 0 := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_SatakeCombination_mul_sum_slotCoeff_div_pow_mul_ite_apply_T_add_T_inv_pow_eq_ite_sqrt_mul_pow_mul_zpow_neg.solution
