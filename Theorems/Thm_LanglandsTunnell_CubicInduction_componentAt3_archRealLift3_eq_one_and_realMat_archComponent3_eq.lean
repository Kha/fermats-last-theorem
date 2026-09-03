import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_componentAt3_archRealLift3_eq_one_and_realMat_archComponent3_eq

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm
open LanglandsTunnell.CubicInduction

theorem LanglandsTunnell.CubicInduction.componentAt3_archRealLift3_eq_one_and_realMat_archComponent3_eq
    (e : Fin 3 → Fin 3 → ℝ) (he : (Matrix.of e).det ≠ 0) :
    (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p (WhittakerBlock.archRealLift3 e) = 1) ∧
    AutomorphicForm.StandardKernel.realMat (archComponent3 (𝓞 ℚ) ℚ (WhittakerBlock.archRealLift3 e)) =
      Matrix.of e ∧
    ((∀ i j : Fin 3, ∑ a : Fin 3, e a i * e a j = if i = j then 1 else 0) →
      archComponent3 (𝓞 ℚ) ℚ (WhittakerBlock.archRealLift3 e) ∈ orth3) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_componentAt3_archRealLift3_eq_one_and_realMat_archComponent3_eq.solution
