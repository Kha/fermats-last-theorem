import Mathlib
import P2M.Util
import P2M.Sol.S_NumberField_AdicCompletion_exists_isCompact_forall_setOf_le_norm_pow_le_subset_smul
attribute [-instance] NumberField.AdelicHaar.locallyCompactSpace_adeleRing NumberField.AdelicHaar.finite_residueField_adicCompletionIntegers NumberField.AdelicHaar.locallyCompactSpace_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_finiteAdeleRing NumberField.AdelicHaar.compactSpace_adicCompletionIntegers NumberField.AdelicHaar.t2Space_finiteAdeleRing NumberField.AdelicHaar.t2Space_matrix_adeleRing NumberField.AdelicHaar.t2Space_adeleRing NumberField.AdelicHaar.fact_isOpen_adicCompletionIntegers NumberField.AdelicHaar.t2Space_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_matrix_adeleRing NumberField.AdelicHaar.t2Space_infiniteAdeleRing NumberField.AdelicHaar.properSpace_adicCompletion

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped Pointwise

theorem NumberField.AdicCompletion.exists_isCompact_forall_setOf_le_norm_pow_le_subset_smul
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (n : ℕ) (hn : 0 < n) (R : ℝ) (hR : 0 < R) :
    ∃ B : Set (v.adicCompletion K), IsCompact B ∧ (0 : v.adicCompletion K) ∉ B ∧
      ∀ a : ℝ, 0 < a → ∃ x₀ : v.adicCompletion K, x₀ ≠ 0 ∧
        {x : v.adicCompletion K | a ≤ ‖x‖ ^ n ∧ ‖x‖ ^ n ≤ a * R} ⊆ x₀ • B := by p2m_exact_reverting @_root_.P2MW.S_NumberField_AdicCompletion_exists_isCompact_forall_setOf_le_norm_pow_le_subset_smul.solution
