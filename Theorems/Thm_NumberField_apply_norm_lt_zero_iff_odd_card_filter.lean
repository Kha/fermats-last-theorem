import Mathlib
import P2M.Util
import P2M.Sol.S_NumberField_apply_norm_lt_zero_iff_odd_card_filter

set_option autoImplicit false

open NumberField
open scoped Classical

universe u v

theorem NumberField.apply_norm_lt_zero_iff_odd_card_filter
    (K : Type u) (F : Type v) [Field K] [NumberField K] [Field F] [NumberField F] [Algebra K F]
    (τ : K →+* ℝ) (β : F) (hβ : β ≠ 0) :
    τ (Algebra.norm K β) < 0 ↔
      Odd (Finset.univ.filter (fun ψ : F →+* ℝ =>
        ψ.comp (algebraMap K F) = τ ∧ ψ β < 0)).card := by p2m_exact_reverting @_root_.P2MW.S_NumberField_apply_norm_lt_zero_iff_odd_card_filter.solution
