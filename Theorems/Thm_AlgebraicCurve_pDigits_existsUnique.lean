import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Differentials
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_pDigits_existsUnique

set_option autoImplicit false

universe u v

open KaehlerDifferential

theorem AlgebraicCurve.pDigits_existsUnique {K : Type u} {F : Type v} [Field K] [Field F]
    [Algebra K F] [AlgebraicCurve.IsCurveOver K F] (p : ℕ) [Fact p.Prime] [CharP K p]
    [PerfectField K] (x : F) [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    {t : F} (hdt : D K F t ≠ 0) (g : F) :
    ∃! a : Fin p → F, g = ∑ i : Fin p, a i ^ p * t ^ (i : ℕ) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_pDigits_existsUnique.solution
