import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_AutomorphicForm_LocalWeightedOrbital
import P2M.Util
import P2M.Sol.S_AutomorphicForm_eq_two_mul_log_mul_sum_of_isWeightedOrbitalIntegral_diagUnits2_of_biInvariant
attribute [-simp] LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open LanglandsTunnell.CubicInduction (diagUnits2)

theorem AutomorphicForm.eq_two_mul_log_mul_sum_of_isWeightedOrbitalIntegral_diagUnits2_of_biInvariant
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (a b : (v.adicCompletion K)ˣ) (hab : a ≠ b)
    (τ : @Measure (AutomorphicForm.localCentralizer K v (diagUnits2 a b))
      (AutomorphicForm.localCentralizerBorel K v (diagUnits2 a b)))
    (hτ : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.localCentralizerBorel K v (diagUnits2 a b)) τ)
    (hτ1 : τ {t | (t : GL (Fin 2) (v.adicCompletion K)) ∈ AutomorphicForm.localIntegralSet K v} = 1)
    (f : GL (Fin 2) (v.adicCompletion K) → ℂ) (hfm : Measurable[AutomorphicForm.localGLBorel K v] f)
    (C : ℝ) (hfC : ∀ g, ‖f g‖ ≤ C)
    (hfK : ∀ g k₁ k₂ : GL (Fin 2) (v.adicCompletion K),
      k₁ ∈ AutomorphicForm.localIntegralSet K v → k₂ ∈ AutomorphicForm.localIntegralSet K v →
        f (k₁ * g * k₂) = f g)
    (ϖ : v.adicCompletion K) (hϖ : ‖ϖ‖ = (Ideal.absNorm v.asIdeal : ℝ)⁻¹) (M : ℕ)
    (hM : ∀ y : v.adicCompletion K,
      f ((AutomorphicForm.unipotentGL2 y)⁻¹ * diagUnits2 a b * AutomorphicForm.unipotentGL2 y) ≠ 0 →
        ‖y‖ ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ M)
    (J : ℂ) (hJ : AutomorphicForm.IsWeightedOrbitalIntegral K v (diagUnits2 a b) τ f J) :
    J = ((2 * Real.log (Ideal.absNorm v.asIdeal) : ℝ) : ℂ) *
      ∑ s ∈ Finset.range M,
        ((((s + 1 : ℕ) : ℝ) * ((Ideal.absNorm v.asIdeal : ℝ) ^ (s + 1) - (Ideal.absNorm v.asIdeal : ℝ) ^ s) : ℝ) : ℂ) *
          f ((AutomorphicForm.unipotentGL2 (ϖ⁻¹ ^ (s + 1)))⁻¹ * diagUnits2 a b *
            AutomorphicForm.unipotentGL2 (ϖ⁻¹ ^ (s + 1))) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_eq_two_mul_log_mul_sum_of_isWeightedOrbitalIntegral_diagUnits2_of_biInvariant.solution
