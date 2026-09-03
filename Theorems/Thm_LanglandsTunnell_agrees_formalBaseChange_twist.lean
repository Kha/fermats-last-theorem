import Definitions.Def_LanglandsTunnell_BcWeight
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_agrees_formalBaseChange_twist

set_option autoImplicit false

open NumberField IsDedekindDomain AutomorphicForm
theorem LanglandsTunnell.agrees_formalBaseChange_twist
    (F K : Type) [Field F] [NumberField F] [Field K] [NumberField K] [Algebra (𝓞 F) (𝓞 K)]
    [Algebra.IsIntegral (𝓞 F) (𝓞 K)] {R : Type*} [CommRing R] (π : HeckeEigensystem F R)
    (χ : HeightOneSpectrum (𝓞 F) → R) :
    (formalBaseChange F K (π.twist χ)).AgreesAwayFromFinite ((formalBaseChange F K π).twist
      (LanglandsTunnell.bcWeight F K χ)) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_agrees_formalBaseChange_twist.solution
