import Definitions.Def_LanglandsTunnell_CubicLambda
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicLambda_zetaEulerPoly_eq_of_resolvent

set_option autoImplicit false

open IsDedekindDomain NumberField LanglandsTunnell.RankinSelberg

theorem LanglandsTunnell.CubicLambda.zetaEulerPoly_eq_of_resolvent
    (K : Type) [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (L : Type) [Field L] [NumberField L] [Algebra (𝓞 ℚ) (𝓞 L)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 L)]
    (E : Type) [Field E] [NumberField E]
    [Algebra (𝓞 ℚ) (𝓞 E)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 E)]
    [Algebra (𝓞 L) (𝓞 E)] [Algebra.IsIntegral (𝓞 L) (𝓞 E)] [IsScalarTower (𝓞 ℚ) (𝓞 L) (𝓞 E)]
    [Algebra (𝓞 K) (𝓞 E)] [Algebra.IsIntegral (𝓞 K) (𝓞 E)] [IsScalarTower (𝓞 ℚ) (𝓞 K) (𝓞 E)]
    [IsGalois ℚ E]
    (hK : Module.finrank ℚ K = 3) (hKn : ¬ Normal ℚ K)
    (hL : Module.finrank ℚ L = 2) (hE : Module.finrank ℚ E = 6)
    (p : HeightOneSpectrum (𝓞 ℚ)) (c : HeightOneSpectrum (𝓞 L) → ℂ)
    (H1 : ∀ (𝔮 : HeightOneSpectrum (𝓞 L)) (𝔔 : HeightOneSpectrum (𝓞 E)), 𝔮.under (𝓞 ℚ) = p →
      𝔔.under (𝓞 L) = 𝔮 → IsPrimitiveRoot (c 𝔮) (𝔮.asIdeal.inertiaDeg' 𝔔.asIdeal))
    (H3 : ∀ 𝔮 𝔮' : HeightOneSpectrum (𝓞 L), 𝔮.under (𝓞 ℚ) = p → 𝔮'.under (𝓞 ℚ) = p → 𝔮 ≠ 𝔮' →
      c 𝔮' = (c 𝔮)⁻¹)
    (hp : ∀ 𝔓 : HeightOneSpectrum (𝓞 E), 𝔓.under (𝓞 ℚ) = p →
      p.asIdeal.ramificationIdx' 𝔓.asIdeal = 1) :
    zetaEulerPoly K p = (Polynomial.C 1 - Polynomial.X) * inducedEulerPoly ℚ c p := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicLambda_zetaEulerPoly_eq_of_resolvent.solution
