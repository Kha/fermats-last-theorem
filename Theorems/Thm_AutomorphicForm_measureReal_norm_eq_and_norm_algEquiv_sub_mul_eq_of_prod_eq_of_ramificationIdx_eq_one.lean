import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import P2M.Util
import P2M.Sol.S_AutomorphicForm_measureReal_norm_eq_and_norm_algEquiv_sub_mul_eq_of_prod_eq_of_ramificationIdx_eq_one

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain

theorem AutomorphicForm.measureReal_norm_eq_and_norm_algEquiv_sub_mul_eq_of_prod_eq_of_ramificationIdx_eq_one
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) (w : v.Extension (𝓞 L))
    (hw : Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w.1).asIdeal w.1.asIdeal = 1)
    (hprime : (Module.finrank (v.adicCompletion K) (w.1.adicCompletion L)).Prime)
    (θ : w.1.adicCompletion L ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)
    (hθ : orderOf θ = Module.finrank (v.adicCompletion K) (w.1.adicCompletion L))
    (hres : ∃ y : w.1.adicCompletion L, ‖y‖ ≤ 1 ∧ ‖θ y - y‖ = 1)
    (c : w.1.adicCompletion L) (n : v.adicCompletion K) (hn : ‖n‖ = 1) (d : ℕ)
    (hd : ‖1 - n‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ (-(d : ℤ)))
    (hc : ∏ i ∈ Finset.range (Module.finrank (v.adicCompletion K) (w.1.adicCompletion L)), (θ ^ i) c =
      algebraMap (v.adicCompletion K) (w.1.adicCompletion L) n)

    (P : ℕ → ℝ) (hP0 : P 0 = 1)
    (hP : ∀ i : ℕ, 1 ≤ i → i ≤ d →
      P i = ((Ideal.absNorm v.asIdeal : ℝ) ^
          ((Module.finrank (v.adicCompletion K) (w.1.adicCompletion L) - 1) * (i - 1)) *
        ∑ t ∈ Finset.range (Module.finrank (v.adicCompletion K) (w.1.adicCompletion L)),
          (Ideal.absNorm v.asIdeal : ℝ) ^ t)⁻¹)
    (hPd : ∀ i : ℕ, d < i → P i = 0)

    [MeasurableSpace (w.1.adicCompletion L)] [BorelSpace (w.1.adicCompletion L)]
    (μE : Measure (w.1.adicCompletion L)) [μE.IsAddHaarMeasure]
    (hμE : μE (w.1.adicCompletionIntegers L : Set (w.1.adicCompletion L)) = 1)
    (m : ℕ) (hm : 1 ≤ m) :
    (∀ y : w.1.adicCompletion L, ‖y‖ = (Ideal.absNorm w.1.asIdeal : ℝ) ^ m →
        ∃ t : ℕ, t ≤ d ∧ ‖θ y - c * y‖ = (Ideal.absNorm w.1.asIdeal : ℝ) ^ ((m : ℤ) - t)) ∧
    (∀ i : ℕ, i ≤ d → i < m →
        (μE {y : w.1.adicCompletion L | ‖y‖ = (Ideal.absNorm w.1.asIdeal : ℝ) ^ m ∧
            ‖θ y - c * y‖ = (Ideal.absNorm w.1.asIdeal : ℝ) ^ (m - i)}).toReal =
          ((Ideal.absNorm w.1.asIdeal : ℝ) ^ m - (Ideal.absNorm w.1.asIdeal : ℝ) ^ (m - 1)) *
            (P i - P (i + 1))) ∧
    (μE {y : w.1.adicCompletion L | ‖y‖ = (Ideal.absNorm w.1.asIdeal : ℝ) ^ m ∧ ‖θ y - c * y‖ ≤ 1}).toReal =
      ((Ideal.absNorm w.1.asIdeal : ℝ) ^ m - (Ideal.absNorm w.1.asIdeal : ℝ) ^ (m - 1)) * P m := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_measureReal_norm_eq_and_norm_algEquiv_sub_mul_eq_of_prod_eq_of_ramificationIdx_eq_one.solution
