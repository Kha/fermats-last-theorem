import Mathlib
import Definitions.Def_AlgebraicCurve_IsCurveOver
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_existsUnique_pDigits_of_D_ne_zero

set_option autoImplicit false

theorem AlgebraicCurve.existsUnique_pDigits_of_D_ne_zero {K : Type*} {F : Type*} [Field K] [Field F]
    [Algebra K F] [AlgebraicCurve.IsCurveOver K F] (p : ℕ) [Fact p.Prime] [CharP K p]
    [PerfectField K] (x : F) [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    {t : F} (hdt : KaehlerDifferential.D K F t ≠ 0) (g : F) :
    ∃! a : Fin p → F, g = ∑ i : Fin p, a i ^ p * t ^ (i : ℕ) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_existsUnique_pDigits_of_D_ne_zero.solution
