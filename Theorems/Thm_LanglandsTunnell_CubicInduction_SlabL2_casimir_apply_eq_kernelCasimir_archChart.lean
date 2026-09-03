import Definitions.Def_LanglandsTunnell_CubicInduction_SlabL2KernelCasimir
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_SlabL2_casimir_apply_eq_kernelCasimir_archChart

set_option autoImplicit false

open Matrix IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.CubicInduction LanglandsTunnell.CubicInduction.SlabL2

theorem LanglandsTunnell.CubicInduction.SlabL2.casimir_apply_eq_kernelCasimir_archChart
    (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hF : WhittakerBlock.IsArchSmooth3 F) (x : AdelicGL 3 (𝓞 ℚ) ℚ) :
    archChart F x (fun a b => if a = b then 1 else 0) = F x ∧
      WhittakerBlock.casimir1 F x = -kernelCasimir1 (archChart F x) (fun a b => if a = b then 1 else 0) ∧
        WhittakerBlock.casimir2 F x = kernelCasimir2 (archChart F x) (fun a b => if a = b then 1 else 0) ∧
          WhittakerBlock.casimir3 F x = -kernelCasimir3T (archChart F x) (fun a b => if a = b then 1 else 0) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_casimir_apply_eq_kernelCasimir_archChart.solution
