import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_Converse_exists_ne_zero_valuation_eq_exp_neg

set_option autoImplicit false

open IsDedekindDomain NumberField

theorem LanglandsTunnell.Converse.exists_ne_zero_valuation_eq_exp_neg (K : Type) [Field K]
    [NumberField K] (S : Finset (HeightOneSpectrum (𝓞 K))) (n : ↥S → ℤ) :
    ∃ α : K, α ≠ 0 ∧ ∀ v : ↥S, v.1.valuation K α = WithZero.exp (-(n v)) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_Converse_exists_ne_zero_valuation_eq_exp_neg.solution
