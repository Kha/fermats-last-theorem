import Mathlib
import P2M.Util
import P2M.Sol.S_IsDedekindDomain_HeightOneSpectrum_relIndex_span_range_mul_norm_det_eq_one_of_forall_mem_span
attribute [-instance] NumberField.AdelicHaar.locallyCompactSpace_adeleRing NumberField.AdelicHaar.finite_residueField_adicCompletionIntegers NumberField.AdelicHaar.locallyCompactSpace_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_finiteAdeleRing NumberField.AdelicHaar.compactSpace_adicCompletionIntegers NumberField.AdelicHaar.t2Space_finiteAdeleRing NumberField.AdelicHaar.t2Space_matrix_adeleRing NumberField.AdelicHaar.t2Space_adeleRing NumberField.AdelicHaar.fact_isOpen_adicCompletionIntegers NumberField.AdelicHaar.t2Space_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_matrix_adeleRing NumberField.AdelicHaar.t2Space_infiniteAdeleRing NumberField.AdelicHaar.properSpace_adicCompletion

set_option autoImplicit false

open NumberField IsDedekindDomain

theorem IsDedekindDomain.HeightOneSpectrum.relIndex_span_range_mul_norm_det_eq_one_of_forall_mem_span
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    {V : Type} [AddCommGroup V] [Module (v.adicCompletion K) V]
    [Module (v.adicCompletionIntegers K) V]
    [IsScalarTower (v.adicCompletionIntegers K) (v.adicCompletion K) V]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (b₁ b₂ : Module.Basis ι (v.adicCompletion K) V)
    (h : ∀ i, b₁ i ∈ Submodule.span (v.adicCompletionIntegers K) (Set.range b₂)) :
    ((Submodule.span (v.adicCompletionIntegers K) (Set.range b₁)).toAddSubgroup.relIndex
        (Submodule.span (v.adicCompletionIntegers K) (Set.range b₂)).toAddSubgroup : ℝ) *
      ‖b₂.det b₁‖ = 1 := by p2m_exact_reverting @_root_.P2MW.S_IsDedekindDomain_HeightOneSpectrum_relIndex_span_range_mul_norm_det_eq_one_of_forall_mem_span.solution
