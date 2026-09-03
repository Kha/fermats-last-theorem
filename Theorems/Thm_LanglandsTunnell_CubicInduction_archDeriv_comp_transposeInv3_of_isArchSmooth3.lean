import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_archDeriv_comp_transposeInv3_of_isArchSmooth3
attribute [-simp] LanglandsTunnell.CubicInduction.WhittakerBlock.coe_archDerivₗ_apply

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm

theorem LanglandsTunnell.CubicInduction.archDeriv_comp_transposeInv3_of_isArchSmooth3
    (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hφ : WhittakerBlock.IsArchSmooth3 φ) (i j : Fin 3) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    WhittakerBlock.archDeriv i j (fun x => φ (transposeInv3 x)) g =
      -WhittakerBlock.archDeriv j i φ (transposeInv3 g) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_archDeriv_comp_transposeInv3_of_isArchSmooth3.solution
