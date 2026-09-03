import Definitions.Def_TwistedUnipotentTerm_SemiLocalOrbitalVocab
import P2M.Util
import P2M.Sol.S_AutomorphicForm_AdelicTracePushforward_exists_pos_forall_integral_localTracePushforward_eq_mul_integral

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct

open scoped TensorProduct.RightActions in
theorem AutomorphicForm.AdelicTracePushforward.exists_pos_forall_integral_localTracePushforward_eq_mul_integral
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K))
    [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]
    (μ : Measure (v.adicCompletion K)) [μ.IsAddHaarMeasure]
    [MeasurableSpace (L ⊗[K] v.adicCompletion K)] [BorelSpace (L ⊗[K] v.adicCompletion K)]
    (ν : Measure (L ⊗[K] v.adicCompletion K)) [ν.IsAddHaarMeasure] :
    ∃ c : ℝ, 0 < c ∧ ∀ Φ : L ⊗[K] v.adicCompletion K → ℂ, IsLocallyConstant Φ → HasCompactSupport Φ →
      ∫ r, AutomorphicForm.AdelicTracePushforward.localTracePushforward K L v Φ r ∂μ = (c : ℂ) * ∫ x, Φ x ∂ν := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_AdelicTracePushforward_exists_pos_forall_integral_localTracePushforward_eq_mul_integral.solution
