import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_LambdaSquared
import Definitions.Def_M4aHerbrand_GenuineDescent
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_RankinSelberg_prod_sq_mul_finprod_localChar_neg_one_mul_neg_one_pow_eq_one_of_finprod_sq_mul_lamSqArch_eq_one_of_not_isBadPlace

set_option autoImplicit false

open IsDedekindDomain NumberField LanglandsTunnell.CubicInduction

open scoped Classical in

theorem LanglandsTunnell.RankinSelberg.prod_sq_mul_finprod_localChar_neg_one_mul_neg_one_pow_eq_one_of_finprod_sq_mul_lamSqArch_eq_one_of_not_isBadPlace
    (K : Type) [Field K] [NumberField K]
    [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (hdeg : Module.finrank ℚ K = 3)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)

    (SQ : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (S' : Finset (HeightOneSpectrum (𝓞 ℚ))) (hSS' : SQ ⊆ S')
    (hgood : ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S' → ¬ IsBadPlace K μ p)

    (ηA : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (hηA : LanglandsTunnell.Converse.IsAdmissibleTwist ℚ ηA)
    (hηoff : ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ SQ → NumberField.TateGlobal.IsUnramifiedCharAt ηA p)
    (t : ℂ) (a : ZMod 2)
    (hηarch : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal), LanglandsTunnell.Converse.IsArchCompAt ℚ ηA w t (a.val : ℤ))

    (lam : HeightOneSpectrum (𝓞 ℚ) → ℂ)
    (hlam1 : ∀ v : HeightOneSpectrum (𝓞 ℚ), ¬ IsBadPlace K μ v → lam v = 1)
    (hlam : (∏ᶠ v : HeightOneSpectrum (𝓞 ℚ), lam v ^ 2) * lamSqArch K = 1) :
    (∏ p ∈ SQ,
        (lam p ^ 2 *
          ((∏ᶠ w ∈ primeFibre ℚ K p,
              ((NumberField.TateGlobal.localChar
                (ηA.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm * μ) w (-1) : ℂˣ) : ℂ)) *
            ∏ᶠ w ∈ primeFibre ℚ K p, ((NumberField.TateGlobal.localChar μ w (-1) : ℂˣ) : ℂ)))) *
        (∏ p ∈ S' \ SQ, lam p ^ 2) *
      ((-1 : ℂ) ^ a.val * (-1 : ℂ) ^ (Finset.univ : Finset {w : InfinitePlace K // w.IsComplex}).card) = 1 := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_RankinSelberg_prod_sq_mul_finprod_localChar_neg_one_mul_neg_one_pow_eq_one_of_finprod_sq_mul_lamSqArch_eq_one_of_not_isBadPlace.solution
