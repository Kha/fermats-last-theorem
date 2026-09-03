import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_LaurentCoeff
import P2M.Util
import P2M.Sol.S_ModularCurve_laurentBaseChange_le_of_divisor_generators_mem

set_option autoImplicit false

open ModularCurve
theorem ModularCurve.laurentBaseChange_le_of_divisor_generators_mem
    (L : Type*) [Field L] [Algebra ℚ L] (M : ℕ) [NeZero M]
    (T : IntermediateField L (LaurentSeries L))
    (hgens : ∀ (d : ℕ) (_ : NeZero d), d ∣ M → coeffEmb L (qExpand ℚ d jq) ∈ T) :
    laurentBaseChange L (modularFunctionFieldFull M) ≤ T := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_laurentBaseChange_le_of_divisor_generators_mem.solution
