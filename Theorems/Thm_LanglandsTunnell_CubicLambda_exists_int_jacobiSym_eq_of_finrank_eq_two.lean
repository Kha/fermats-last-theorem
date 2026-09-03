import Definitions.Def_LanglandsTunnell_CubicLambda
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicLambda_exists_int_jacobiSym_eq_of_finrank_eq_two

set_option autoImplicit false

open IsDedekindDomain NumberField

theorem LanglandsTunnell.CubicLambda.exists_int_jacobiSym_eq_of_finrank_eq_two
    (L : Type) [Field L] [NumberField L] [Algebra (𝓞 ℚ) (𝓞 L)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 L)]
    (hL : Module.finrank ℚ L = 2) :
    ∃ d : ℤ, d ≠ 0 ∧ (d < 0 ↔ InfinitePlace.nrComplexPlaces L ≠ 0) ∧
      ∀ (ℓ : ℕ), ℓ.Prime → ¬ (ℓ : ℤ) ∣ 2 * d →
        ∀ (p : HeightOneSpectrum (𝓞 ℚ)), (ℓ : 𝓞 ℚ) ∈ p.asIdeal →
          ∀ (𝔮 : HeightOneSpectrum (𝓞 L)), 𝔮.under (𝓞 ℚ) = p →
            p.asIdeal.ramificationIdx' 𝔮.asIdeal = 1 ∧
              (p.asIdeal.inertiaDeg' 𝔮.asIdeal = 1 → jacobiSym d ℓ = 1) ∧
              (p.asIdeal.inertiaDeg' 𝔮.asIdeal = 2 → jacobiSym d ℓ = -1) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicLambda_exists_int_jacobiSym_eq_of_finrank_eq_two.solution
