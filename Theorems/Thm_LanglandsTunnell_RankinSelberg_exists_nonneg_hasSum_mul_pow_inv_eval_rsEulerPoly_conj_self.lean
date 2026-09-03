import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_RankinSelberg_exists_nonneg_hasSum_mul_pow_inv_eval_rsEulerPoly_conj_self
attribute [-instance] NumberField.AdelicHaar.locallyCompactSpace_adeleRing NumberField.AdelicHaar.finite_residueField_adicCompletionIntegers NumberField.AdelicHaar.locallyCompactSpace_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_finiteAdeleRing NumberField.AdelicHaar.compactSpace_adicCompletionIntegers NumberField.AdelicHaar.t2Space_finiteAdeleRing NumberField.AdelicHaar.t2Space_matrix_adeleRing NumberField.AdelicHaar.t2Space_adeleRing NumberField.AdelicHaar.fact_isOpen_adicCompletionIntegers NumberField.AdelicHaar.t2Space_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_matrix_adeleRing NumberField.AdelicHaar.t2Space_infiniteAdeleRing NumberField.AdelicHaar.properSpace_adicCompletion
attribute [-simp] AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed

set_option autoImplicit false

open LanglandsTunnell.RankinSelberg

theorem LanglandsTunnell.RankinSelberg.exists_nonneg_hasSum_mul_pow_inv_eval_rsEulerPoly_conj_self
    (a b : ℂ) :
    ∃ e : ℕ → ℝ, e 0 = 1 ∧ e 1 = ‖a‖ ^ 2 ∧ (∀ n : ℕ, 0 ≤ e n) ∧
      (∀ n : ℕ, e n ≤ (2 * (‖a‖ + ‖b‖ + 1)) ^ (2 * n)) ∧
      ∀ y : ℂ, ‖y‖ * (‖a‖ + ‖b‖ + 1) ^ 2 < 1 →
        HasSum (fun n : ℕ => (e n : ℂ) * y ^ n)
          ((rsEulerPoly ((starRingEnd ℂ) a) ((starRingEnd ℂ) b) a b 0).eval y)⁻¹ := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_RankinSelberg_exists_nonneg_hasSum_mul_pow_inv_eval_rsEulerPoly_conj_self.solution
