import Mathlib
import P2M.Util
import P2M.Sol.S_MeasureTheory_memLp_two_and_integral_sum_norm_sq_sub_le_mul_add_of_eq_mul_add_sum_conj_mul_of_bessel

set_option autoImplicit false

open MeasureTheory
open scoped ComplexConjugate

theorem MeasureTheory.memLp_two_and_integral_sum_norm_sq_sub_le_mul_add_of_eq_mul_add_sum_conj_mul_of_bessel
    {n m : ℕ} (κ τ₁ τ₂ : ℝ)
    (T F d : Fin n → ℝ → ℂ) (d' : Fin m → ℝ → ℂ) (B : Fin n → Fin m → ℝ → ℂ)
    (_hd : ∀ j, MemLp (d j) 2) (_hd' : ∀ j', MemLp (d' j') 2)
    (_hTF : ∀ j, AEStronglyMeasurable (fun t => T j t - F j t))
    (_hB : ∀ (t : ℝ) (x : Fin m → ℂ),
      ∑ j : Fin n, ‖∑ j' : Fin m, conj (B j j' t) * x j'‖ ^ 2 ≤ ∑ j' : Fin m, ‖x j'‖ ^ 2)
    (_heq : ∀ (j : Fin n) (t : ℝ),
      T j (t + τ₁) - F j (t + τ₁) = (κ : ℂ) * (d j (t + τ₁) + ∑ j' : Fin m, conj (B j j' t) * d' j' (-t + τ₂))) :
    (∀ j : Fin n, MemLp (fun t => F j t - T j t) 2) ∧
    ∫ t : ℝ, ∑ j : Fin n, ‖F j t - T j t‖ ^ 2 ≤
      2 * κ ^ 2 * ((∑ j : Fin n, ∫ t : ℝ, ‖d j t‖ ^ 2) + ∑ j' : Fin m, ∫ t : ℝ, ‖d' j' t‖ ^ 2) := by p2m_exact_reverting @_root_.P2MW.S_MeasureTheory_memLp_two_and_integral_sum_norm_sq_sub_le_mul_add_of_eq_mul_add_sum_conj_mul_of_bessel.solution
