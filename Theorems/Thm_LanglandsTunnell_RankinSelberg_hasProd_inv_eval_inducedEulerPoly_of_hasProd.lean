import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_RankinSelberg_hasProd_inv_eval_inducedEulerPoly_of_hasProd

set_option autoImplicit false

open IsDedekindDomain NumberField

theorem LanglandsTunnell.RankinSelberg.hasProd_inv_eval_inducedEulerPoly_of_hasProd
    (F K : Type) [Field F] [NumberField F] [Field K] [NumberField K] [Algebra (𝓞 F) (𝓞 K)]
    [Algebra.IsIntegral (𝓞 F) (𝓞 K)] (c : HeightOneSpectrum (𝓞 K) → ℂ) (s Z : ℂ)
    (h : HasProd (fun 𝔓 : HeightOneSpectrum (𝓞 K) =>
      (1 - c 𝔓 * ((Ideal.absNorm 𝔓.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹) Z) :
    HasProd (fun p : HeightOneSpectrum (𝓞 F) =>
      ((inducedEulerPoly F c p).eval (((Ideal.absNorm p.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹) Z := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_RankinSelberg_hasProd_inv_eval_inducedEulerPoly_of_hasProd.solution
