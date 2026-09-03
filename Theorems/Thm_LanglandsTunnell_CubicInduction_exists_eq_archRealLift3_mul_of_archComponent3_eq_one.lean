import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_exists_eq_archRealLift3_mul_of_archComponent3_eq_one

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm
open LanglandsTunnell.CubicInduction

theorem LanglandsTunnell.CubicInduction.exists_eq_archRealLift3_mul_of_archComponent3_eq_one
    (k₀ : AdelicGL 3 (𝓞 ℚ) ℚ) :
    ∃ (c : Fin 3 → Fin 3 → ℝ) (k₁ : AdelicGL 3 (𝓞 ℚ) ℚ), (Matrix.of c).det ≠ 0 ∧ archComponent3 (𝓞 ℚ) ℚ k₁ = 1 ∧
      k₀ = WhittakerBlock.archRealLift3 c * k₁ := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_archRealLift3_mul_of_archComponent3_eq_one.solution
