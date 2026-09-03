import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_WhittakerBlock_hasDerivAt_comp_archRealLift3_rotation_of_isArchSmooth3

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm

theorem LanglandsTunnell.CubicInduction.WhittakerBlock.hasDerivAt_comp_archRealLift3_rotation_of_isArchSmooth3
    (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hφ : WhittakerBlock.IsArchSmooth3 φ) (c₁ c₂ : Fin 3)
    (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    HasDerivAt
      (fun s : ℝ => φ (g * WhittakerBlock.archRealLift3 (fun i j =>
        if i = c₁ ∧ j = c₁ then Real.cos s else if i = c₂ ∧ j = c₂ then Real.cos s else
        if i = c₁ ∧ j = c₂ then - Real.sin s else if i = c₂ ∧ j = c₁ then Real.sin s else
        if i = j then 1 else 0)))
      (archDeriv c₂ c₁ φ g - archDeriv c₁ c₂ φ g) 0 := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_WhittakerBlock_hasDerivAt_comp_archRealLift3_rotation_of_isArchSmooth3.solution
