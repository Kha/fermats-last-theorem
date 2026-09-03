import Definitions.Def_AutomorphicForm_FormalBaseChange
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_formalBaseChange_twist_rpow_absNorm_agreesAwayFromFinite
attribute [-simp] LanglandsTunnell.bcWeight_apply

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm
theorem LanglandsTunnell.formalBaseChange_twist_rpow_absNorm_agreesAwayFromFinite
    (F K : Type) [Field F] [NumberField F] [Field K] [NumberField K]
    [Algebra (𝓞 F) (𝓞 K)] [Algebra.IsIntegral (𝓞 F) (𝓞 K)]
    (Φ : HeckeEigensystem F ℂ) (t : ℝ) :
    (formalBaseChange F K (Φ.twist (fun v : HeightOneSpectrum (𝓞 F) => (((Ideal.absNorm v.asIdeal : ℝ) ^ (-t) : ℝ) : ℂ)))).AgreesAwayFromFinite
      ((formalBaseChange F K Φ).twist (fun v : HeightOneSpectrum (𝓞 K) => (((Ideal.absNorm v.asIdeal : ℝ) ^ (-t) : ℝ) : ℂ))) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_formalBaseChange_twist_rpow_absNorm_agreesAwayFromFinite.solution
