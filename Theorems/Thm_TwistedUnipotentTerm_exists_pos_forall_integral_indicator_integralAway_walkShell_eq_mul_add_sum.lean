import Definitions.Def_TwistedUnipotentTerm_SemiLocalOrbitalVocab
import P2M.Util
import P2M.Sol.S_TwistedUnipotentTerm_exists_pos_forall_integral_indicator_integralAway_walkShell_eq_mul_add_sum

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct

open scoped TensorProduct.RightActions in
theorem TwistedUnipotentTerm.exists_pos_forall_integral_indicator_integralAway_walkShell_eq_mul_add_sum
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) (w : v.Extension (𝓞 L))
    [MeasurableSpace (L ⊗[K] v.adicCompletion K)] [BorelSpace (L ⊗[K] v.adicCompletion K)]
    (ν : Measure (L ⊗[K] v.adicCompletion K)) [ν.IsAddHaarMeasure] :
    ∃ c : ℝ, 0 < c ∧ ∀ (h : ℕ → ℂ) (R : ℕ), (∀ r, R < r → h r = 0) →
      ∫ x, {x : L ⊗[K] v.adicCompletion K | ∀ w' : v.Extension (𝓞 L), w' ≠ w →
              HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v x w' ∈
                w'.1.adicCompletionIntegers L}.indicator
          (fun x => h (WithZero.log (Valued.v
            (HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v x w))).toNat) x ∂ν =
        (c : ℂ) * (h 0 + ∑ r ∈ Finset.Icc 1 R, h r *
          ((Ideal.absNorm w.1.asIdeal : ℂ) ^ r - (Ideal.absNorm w.1.asIdeal : ℂ) ^ (r - 1))) := by p2m_exact_reverting @_root_.P2MW.S_TwistedUnipotentTerm_exists_pos_forall_integral_indicator_integralAway_walkShell_eq_mul_add_sum.solution
