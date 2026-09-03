import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_isGaugeMajorised3_of_mem_gl3CyclicSubspace

set_option autoImplicit false

open IsDedekindDomain NumberField LanglandsTunnell.CubicInduction

theorem LanglandsTunnell.CubicInduction.isGaugeMajorised3_of_mem_gl3CyclicSubspace (F : Type) [Field F] [NumberField F]
    {W : AdelicGL 3 (𝓞 F) F → ℂ} (hW : IsGaugeMajorised3 F W) {W' : AdelicGL 3 (𝓞 F) F → ℂ}
    (hW' : W' ∈ gl3CyclicSubspace W) : IsGaugeMajorised3 F W' := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_isGaugeMajorised3_of_mem_gl3CyclicSubspace.solution
