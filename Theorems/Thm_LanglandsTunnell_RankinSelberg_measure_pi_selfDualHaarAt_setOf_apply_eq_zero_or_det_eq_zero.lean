import Definitions.Def_LanglandsTunnell_CubicInduction_GodementSection
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_RankinSelberg_measure_pi_selfDualHaarAt_setOf_apply_eq_zero_or_det_eq_zero

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory AutomorphicForm LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction
open scoped ENNReal

theorem LanglandsTunnell.RankinSelberg.measure_pi_selfDualHaarAt_setOf_apply_eq_zero_or_det_eq_zero
    (p : HeightOneSpectrum (𝓞 ℚ)) :
    letI : MeasurableSpace (p.adicCompletion ℚ) := localBorel ℚ p
    (MeasureTheory.Measure.pi fun _ : Fin 2 => MeasureTheory.Measure.pi fun _ : Fin 2 => selfDualHaarAt ℚ p)
        {X : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) | X 0 0 = 0 ∨ X.det = 0} = 0 := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_RankinSelberg_measure_pi_selfDualHaarAt_setOf_apply_eq_zero_or_det_eq_zero.solution
