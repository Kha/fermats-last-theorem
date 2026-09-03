import Mathlib
import P2M.Util
import P2M.Sol.S_NumberField_exists_forall_finite_and_ncard_le_setOf_forall_valuation_eq_of_forall_apply_mem_Icc

set_option autoImplicit false

open NumberField IsDedekindDomain

theorem NumberField.exists_forall_finite_and_ncard_le_setOf_forall_valuation_eq_of_forall_apply_mem_Icc
    (K : Type*) [Field K] [NumberField K] (c₁ c₂ : ℝ) (hc₁ : 0 < c₁) :
    ∃ C : ℕ, ∀ e : HeightOneSpectrum (𝓞 K) → WithZero (Multiplicative ℤ),
      {x : K | (∀ v : HeightOneSpectrum (𝓞 K), v.valuation K x = e v) ∧
          ∀ w : InfinitePlace K, w x ∈ Set.Icc c₁ c₂}.Finite ∧
      {x : K | (∀ v : HeightOneSpectrum (𝓞 K), v.valuation K x = e v) ∧
          ∀ w : InfinitePlace K, w x ∈ Set.Icc c₁ c₂}.ncard ≤ C := by p2m_exact_reverting @_root_.P2MW.S_NumberField_exists_forall_finite_and_ncard_le_setOf_forall_valuation_eq_of_forall_apply_mem_Icc.solution
