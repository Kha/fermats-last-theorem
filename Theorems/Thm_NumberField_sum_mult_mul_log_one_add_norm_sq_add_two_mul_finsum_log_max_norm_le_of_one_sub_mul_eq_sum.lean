import Mathlib
import P2M.Util
import P2M.Sol.S_NumberField_sum_mult_mul_log_one_add_norm_sq_add_two_mul_finsum_log_max_norm_le_of_one_sub_mul_eq_sum

set_option autoImplicit false

p2m_open "NumberField~finsum_posLog_inv_norm_one_sub_add_sum_mult_mul_posLog_inv_le IsDedekindDomain"

theorem NumberField.sum_mult_mul_log_one_add_norm_sq_add_two_mul_finsum_log_max_norm_le_of_one_sub_mul_eq_sum
    (F : Type) [Field F] [NumberField F] (c : F) (hc : c ≠ 1) (ℓ : ℕ)
    (x : AdeleRing (𝓞 F) F) (P U Q : ℕ → AdeleRing (𝓞 F) F)
    (hx : algebraMap F (AdeleRing (𝓞 F) F) (1 - c) * x = ∑ j ∈ Finset.range ℓ, P j * U j)
    (hcQ : algebraMap F (AdeleRing (𝓞 F) F) c = ∏ i ∈ Finset.range ℓ, Q i)
    (W : Finset (HeightOneSpectrum (𝓞 F))) (Λ : HeightOneSpectrum (𝓞 F) → ℝ) (Λinf : InfinitePlace F → ℝ)
    (hΛ : ∀ w, 1 ≤ Λ w) (hΛW : ∀ w, w ∉ W → Λ w = 1) (hΛinf : ∀ w, 1 ≤ Λinf w)
    (hP : ∀ j, j < ℓ → (∀ w : HeightOneSpectrum (𝓞 F), ‖(P j).2 w‖ ≤ Λ w) ∧ ∀ w : InfinitePlace F, ‖(P j).1 w‖ ≤ Λinf w)
    (hU : ∀ j, j < ℓ → (∀ w : HeightOneSpectrum (𝓞 F), ‖(U j).2 w‖ ≤ Λ w) ∧ ∀ w : InfinitePlace F, ‖(U j).1 w‖ ≤ Λinf w)
    (hQ : ∀ i, i < ℓ → (∀ w : HeightOneSpectrum (𝓞 F), ‖(Q i).2 w‖ ≤ Λ w) ∧ ∀ w : InfinitePlace F, ‖(Q i).1 w‖ ≤ Λinf w) :
    (∑ w : InfinitePlace F, (w.mult : ℝ) * Real.log (1 + ‖x.1 w‖ ^ 2)) +
        2 * ∑ᶠ v : HeightOneSpectrum (𝓞 F), Real.log (max 1 ‖x.2 v‖) ≤
      (2 * ℓ + 4) * ((∑ w ∈ W, Real.log (Λ w)) + ∑ w : InfinitePlace F, (w.mult : ℝ) * Real.log (Λinf w)) +
        (4 * Real.log 2 + 2 * Real.log ℓ) * ∑ w : InfinitePlace F, (w.mult : ℝ) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_sum_mult_mul_log_one_add_norm_sq_add_two_mul_finsum_log_max_norm_le_of_one_sub_mul_eq_sum.solution
