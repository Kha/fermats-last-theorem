import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_isCentreFinite_comp_transposeInv3_of_isArchSmooth3
attribute [-simp] LanglandsTunnell.CubicInduction.WhittakerBlock.coe_archDerivₗ_apply

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm
open LanglandsTunnell.CubicInduction.WhittakerBlock (IsCentreFinite)

theorem LanglandsTunnell.CubicInduction.isCentreFinite_comp_transposeInv3_of_isArchSmooth3
    (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hφ : WhittakerBlock.IsArchSmooth3 φ) (hz : IsCentreFinite φ) :
    IsCentreFinite (fun x => φ (transposeInv3 x)) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_isCentreFinite_comp_transposeInv3_of_isArchSmooth3.solution
