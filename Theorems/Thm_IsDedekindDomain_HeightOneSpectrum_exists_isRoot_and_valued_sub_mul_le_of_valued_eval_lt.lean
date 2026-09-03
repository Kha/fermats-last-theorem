import Mathlib
import P2M.Util
import P2M.Sol.S_IsDedekindDomain_HeightOneSpectrum_exists_isRoot_and_valued_sub_mul_le_of_valued_eval_lt
set_option autoImplicit false
open NumberField IsDedekindDomain

theorem IsDedekindDomain.HeightOneSpectrum.exists_isRoot_and_valued_sub_mul_le_of_valued_eval_lt
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (f : Polynomial ↥(v.adicCompletionIntegers K)) (a₀ : ↥(v.adicCompletionIntegers K))
    (h : Valued.v ((f.eval a₀ : ↥(v.adicCompletionIntegers K)) : v.adicCompletion K) <
      Valued.v ((f.derivative.eval a₀ : ↥(v.adicCompletionIntegers K)) : v.adicCompletion K) ^ 2) :
    ∃ a : ↥(v.adicCompletionIntegers K), f.IsRoot a ∧
      Valued.v ((a : v.adicCompletion K) - (a₀ : v.adicCompletion K)) *
          Valued.v ((f.derivative.eval a₀ : ↥(v.adicCompletionIntegers K)) : v.adicCompletion K) ≤
        Valued.v ((f.eval a₀ : ↥(v.adicCompletionIntegers K)) : v.adicCompletion K) := by p2m_exact_reverting @_root_.P2MW.S_IsDedekindDomain_HeightOneSpectrum_exists_isRoot_and_valued_sub_mul_le_of_valued_eval_lt.solution
