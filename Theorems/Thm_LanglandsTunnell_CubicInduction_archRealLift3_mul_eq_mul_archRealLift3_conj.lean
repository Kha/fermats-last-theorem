import Definitions.Def_LanglandsTunnell_CubicInduction_ArchSmooth3
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_archRealLift3_mul_eq_mul_archRealLift3_conj

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm
open LanglandsTunnell.CubicInduction

theorem LanglandsTunnell.CubicInduction.archRealLift3_mul_eq_mul_archRealLift3_conj
    (g : AdelicGL 3 (𝓞 ℚ) ℚ) (m : Fin 3 → Fin 3 → ℝ) (hm : (Matrix.of m).det ≠ 0) :
    (AutomorphicForm.StandardKernel.realMat (archComponent3 (𝓞 ℚ) ℚ g)).det ≠ 0 ∧
    WhittakerBlock.archRealLift3 m * g =
      g * WhittakerBlock.archRealLift3 (fun a b =>
        ((AutomorphicForm.StandardKernel.realMat (archComponent3 (𝓞 ℚ) ℚ g))⁻¹ * Matrix.of m *
          AutomorphicForm.StandardKernel.realMat (archComponent3 (𝓞 ℚ) ℚ g)) a b) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_archRealLift3_mul_eq_mul_archRealLift3_conj.solution
