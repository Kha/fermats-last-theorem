import Mathlib
import P2M.Util
import P2M.Sol.S_MeasureTheory_integrable_norm_sq_sum_conj_smul_and_integral_eq_sum_mul_norm_sq_of_forall_integral_mul_conj_eq

set_option autoImplicit false

open MeasureTheory
open scoped ComplexConjugate

theorem MeasureTheory.integrable_norm_sq_sum_conj_smul_and_integral_eq_sum_mul_norm_sq_of_forall_integral_mul_conj_eq
    {X : Type*} [MeasurableSpace X] (ρ : Measure X)
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {J : Type*} [Fintype J] [DecidableEq J]
    (φ : J → X → ℂ) (hφ : ∀ j, MemLp (φ j) 2 ρ) (v : J → E) (s : J → ℝ)
    (horth : ∀ j j', ∫ x, φ j x * conj (φ j' x) ∂ρ = if j = j' then ((s j : ℝ) : ℂ) else 0) :
    Integrable (fun x => ‖∑ j, conj (φ j x) • v j‖ ^ 2) ρ ∧
      ∫ x, ‖∑ j, conj (φ j x) • v j‖ ^ 2 ∂ρ = ∑ j, s j * ‖v j‖ ^ 2 := by p2m_exact_reverting @_root_.P2MW.S_MeasureTheory_integrable_norm_sq_sum_conj_smul_and_integral_eq_sum_mul_norm_sq_of_forall_integral_mul_conj_eq.solution
