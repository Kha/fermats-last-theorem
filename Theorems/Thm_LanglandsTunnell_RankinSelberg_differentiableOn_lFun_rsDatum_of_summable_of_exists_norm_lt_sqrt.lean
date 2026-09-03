import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_HeckeEigenfunction
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_RankinSelberg_differentiableOn_lFun_rsDatum_of_summable_of_exists_norm_lt_sqrt
attribute [-simp] AutomorphicForm.JPSSCubicLiftPackage.mk.sizeOf_spec AutomorphicForm.formalBaseChange_a AutomorphicForm.JPSSCubicLiftPackage.mk.injEq AutomorphicForm.formalBaseChange_b

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm NumberField.TateGlobal
open scoped Classical in

theorem LanglandsTunnell.RankinSelberg.differentiableOn_lFun_rsDatum_of_summable_of_exists_norm_lt_sqrt
    (K : Type) [Field K] [NumberField K]
    [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (hdeg : Module.finrank ℚ K = 3)
    (Pi : HeckeEigensystem ℚ ℂ)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (SQ : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (gammaR gammaC gammaRDual gammaCDual : Multiset ℂ)
    (hμ : ∀ 𝔓 : HeightOneSpectrum (𝓞 K), IsUnramifiedCharAt μ 𝔓 →
      ‖((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ)‖ = 1)
    (hb : ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ SQ → ‖Pi.b p‖ = 1)
    (ha : ∀ σ : ℝ, 1 < σ →
      Summable fun p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ) =>
        ‖Pi.a p‖ * (Ideal.absNorm p.asIdeal : ℝ) ^ (-σ))
    (hroot : ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ SQ → ∃ γ δ : ℂ, γ + δ = Pi.a p ∧ γ * δ = Pi.b p ∧
      ‖γ‖ < Real.sqrt (Ideal.absNorm p.asIdeal) ∧ ‖δ‖ < Real.sqrt (Ideal.absNorm p.asIdeal)) :
    DifferentiableOn ℂ
      (rsDatum ℚ SQ Pi.a Pi.b
        (fun 𝔓 => if IsUnramifiedCharAt μ 𝔓 then ((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) else 0)
        gammaR gammaC gammaRDual gammaCDual).LFun
      {s : ℂ |
        (rsDatum ℚ SQ Pi.a Pi.b
          (fun 𝔓 => if IsUnramifiedCharAt μ 𝔓 then ((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) else 0)
          gammaR gammaC gammaRDual gammaCDual).abscissa < s.re} ∧
    DifferentiableOn ℂ
      (rsDatum ℚ SQ Pi.a Pi.b
        (fun 𝔓 => if IsUnramifiedCharAt μ 𝔓 then ((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) else 0)
        gammaR gammaC gammaRDual gammaCDual).LFunDual
      {s : ℂ |
        (rsDatum ℚ SQ Pi.a Pi.b
          (fun 𝔓 => if IsUnramifiedCharAt μ 𝔓 then ((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) else 0)
          gammaR gammaC gammaRDual gammaCDual).abscissa < s.re} := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_RankinSelberg_differentiableOn_lFun_rsDatum_of_summable_of_exists_norm_lt_sqrt.solution
