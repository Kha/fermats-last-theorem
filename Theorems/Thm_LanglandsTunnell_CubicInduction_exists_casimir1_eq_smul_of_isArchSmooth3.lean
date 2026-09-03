import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_exists_casimir1_eq_smul_of_isArchSmooth3

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm

theorem
LanglandsTunnell.CubicInduction.exists_casimir1_eq_smul_of_isArchSmooth3
    (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (hcen : ∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
      u (centralScalarGL 3 (𝓞 ℚ) ℚ z * g) = (ω z : ℂ) * u g)
    (hsa : WhittakerBlock.IsArchSmooth3 u) :
    ∃ c : ℂ, WhittakerBlock.casimir1 u = c • u := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_exists_casimir1_eq_smul_of_isArchSmooth3.solution
