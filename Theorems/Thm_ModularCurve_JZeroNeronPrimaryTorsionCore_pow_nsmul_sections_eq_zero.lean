import Definitions.Def_ModularCurve_JZeroNeronPrimaryTorsionSheaf
import P2M.Util
import P2M.Sol.S_ModularCurve_JZeroNeronPrimaryTorsionCore_pow_nsmul_sections_eq_zero
open ModularCurve AlgebraicGeometry AlgebraicGeometry.Scheme ValuationSubring
theorem ModularCurve.JZeroNeronPrimaryTorsionCore.pow_nsmul_sections_eq_zero
    (p : ℕ) [Fact p.Prime] (q : ℕ) [Fact q.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (C : JZeroNeronPrimaryTorsionCore p q A hA) (m : ℕ)
    (U : specInt.Fppf) (s : (C.𝒥 m).1.obj (Opposite.op U)) :
    q ^ m • s = 0 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_JZeroNeronPrimaryTorsionCore_pow_nsmul_sections_eq_zero.solution
