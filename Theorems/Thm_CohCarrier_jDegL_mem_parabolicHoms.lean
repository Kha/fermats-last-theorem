import Definitions.Def_CohCarrier_Level
import Definitions.Def_ModularCurve_PeriodMap
import P2M.Util
import P2M.Sol.S_CohCarrier_jDegL_mem_parabolicHoms

set_option autoImplicit false

theorem CohCarrier.jDegL_mem_parabolicHoms (M M' d : ℕ) [NeZero M'] [NeZero d]
    (A : Type*) [AddCommGroup A] (R : Type*) [Semiring R] [Module R A]
    (h : CohCarrier.LevelLE M M' ⊤ ⊤ d) (y : CohCarrier.H1 M' ⊤ A)
    (hy : y ∈ ModularCurve.Period.parabolicHoms R (CohCarrier.GammaH M' ⊤) A) :
    CohCarrier.jDegL M M' ⊤ ⊤ d A R h y ∈ ModularCurve.Period.parabolicHoms R (CohCarrier.GammaH M ⊤) A := by p2m_exact_reverting @_root_.P2MW.S_CohCarrier_jDegL_mem_parabolicHoms.solution
