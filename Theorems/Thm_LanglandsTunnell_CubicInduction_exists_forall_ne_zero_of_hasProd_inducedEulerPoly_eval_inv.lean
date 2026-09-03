import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_LanglandsTunnell_CubicLambda
import Definitions.Def_LanglandsTunnell_CubicInduction_DataOn
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_exists_forall_ne_zero_of_hasProd_inducedEulerPoly_eval_inv

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.TateGlobal AutomorphicForm LanglandsTunnell.Converse
  LanglandsTunnell.CubicInduction LanglandsTunnell.TateLocal MeasureTheory LanglandsTunnell.RankinSelberg

theorem LanglandsTunnell.CubicInduction.exists_forall_ne_zero_of_hasProd_inducedEulerPoly_eval_inv
    (K : Type) [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (_hdeg : Module.finrank ℚ K = 3)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (_hμ : IsAdmissibleTwist K μ)
    (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (τ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (_hτ : IsAdmissibleTwist ℚ τ) :
    ∃ σL : ℝ, ∀ s : ℂ, σL < s.re → ∀ L : ℂ,
      HasProd (fun p : {p : HeightOneSpectrum (𝓞 ℚ) // p ∉ S} =>
          ((inducedEulerPoly ℚ (inducedCoeff K μ) p.1).eval
            (LanglandsTunnell.CubicLambda.eulerCoeff ℚ τ p.1 * (Ideal.absNorm p.1.asIdeal : ℂ) ^ (-s)))⁻¹) L →
      L ≠ 0 := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_ne_zero_of_hasProd_inducedEulerPoly_eval_inv.solution
