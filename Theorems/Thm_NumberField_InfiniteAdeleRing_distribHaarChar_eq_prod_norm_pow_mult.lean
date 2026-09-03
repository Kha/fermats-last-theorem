import Mathlib
import P2M.Util
import P2M.Sol.S_NumberField_InfiniteAdeleRing_distribHaarChar_eq_prod_norm_pow_mult
attribute [-instance] NumberField.AdelicHaar.locallyCompactSpace_adeleRing NumberField.AdelicHaar.finite_residueField_adicCompletionIntegers NumberField.AdelicHaar.locallyCompactSpace_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_finiteAdeleRing NumberField.AdelicHaar.compactSpace_adicCompletionIntegers NumberField.AdelicHaar.t2Space_finiteAdeleRing NumberField.AdelicHaar.t2Space_matrix_adeleRing NumberField.AdelicHaar.t2Space_adeleRing NumberField.AdelicHaar.fact_isOpen_adicCompletionIntegers NumberField.AdelicHaar.t2Space_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_matrix_adeleRing NumberField.AdelicHaar.t2Space_infiniteAdeleRing NumberField.AdelicHaar.properSpace_adicCompletion

set_option autoImplicit false

open MeasureTheory NumberField

theorem NumberField.InfiniteAdeleRing.distribHaarChar_eq_prod_norm_pow_mult
    (K : Type) [Field K] [NumberField K]
    [MeasurableSpace (InfiniteAdeleRing K)] [BorelSpace (InfiniteAdeleRing K)]
    (a : (InfiniteAdeleRing K)ˣ) :
    (distribHaarChar (InfiniteAdeleRing K) a : ℝ) = ∏ w : InfinitePlace K, ‖(a : InfiniteAdeleRing K) w‖ ^ w.mult := by p2m_exact_reverting @_root_.P2MW.S_NumberField_InfiniteAdeleRing_distribHaarChar_eq_prod_norm_pow_mult.solution
