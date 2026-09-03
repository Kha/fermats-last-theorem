import Definitions.Def_AutomorphicForm_FormalBaseChange
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_formalBaseChange_twist_rpow_absNorm_a_eq_and_b_eq

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm
theorem LanglandsTunnell.formalBaseChange_twist_rpow_absNorm_a_eq_and_b_eq
    (F K : Type) [Field F] [NumberField F] [Field K] [NumberField K]
    [Algebra (𝓞 F) (𝓞 K)] [Algebra.IsIntegral (𝓞 F) (𝓞 K)]
    (Φ : HeckeEigensystem F ℂ) (t : ℝ) (𝔓 : HeightOneSpectrum (𝓞 K)) :
    (formalBaseChange F K (Φ.twist (fun v : HeightOneSpectrum (𝓞 F) => (((Ideal.absNorm v.asIdeal : ℝ) ^ (-t) : ℝ) : ℂ)))).a 𝔓 =
      ((formalBaseChange F K Φ).twist (fun v : HeightOneSpectrum (𝓞 K) => (((Ideal.absNorm v.asIdeal : ℝ) ^ (-t) : ℝ) : ℂ))).a 𝔓 ∧
    (formalBaseChange F K (Φ.twist (fun v : HeightOneSpectrum (𝓞 F) => (((Ideal.absNorm v.asIdeal : ℝ) ^ (-t) : ℝ) : ℂ)))).b 𝔓 =
      ((formalBaseChange F K Φ).twist (fun v : HeightOneSpectrum (𝓞 K) => (((Ideal.absNorm v.asIdeal : ℝ) ^ (-t) : ℝ) : ℂ))).b 𝔓 := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_formalBaseChange_twist_rpow_absNorm_a_eq_and_b_eq.solution
