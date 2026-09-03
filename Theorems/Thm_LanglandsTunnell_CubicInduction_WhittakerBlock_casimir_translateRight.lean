import Definitions.Def_LanglandsTunnell_CubicInduction_SlabL2Cusp
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_WhittakerBlock_casimir_translateRight
attribute [-simp] LanglandsTunnell.CubicInduction.WhittakerBlock.coe_archDerivₗ_apply

set_option autoImplicit false

open NumberField IsDedekindDomain AutomorphicForm

theorem LanglandsTunnell.CubicInduction.WhittakerBlock.casimir_translateRight
    (H : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hH : WhittakerBlock.IsArchSmooth3 H) (y : AdelicGL 3 (𝓞 ℚ) ℚ) :
    casimir1 (SlabL2.translateRight y H) = SlabL2.translateRight y (casimir1 H) ∧
      casimir2 (SlabL2.translateRight y H) = SlabL2.translateRight y (casimir2 H) ∧
        casimir3 (SlabL2.translateRight y H) = SlabL2.translateRight y (casimir3 H) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_WhittakerBlock_casimir_translateRight.solution
