import Definitions.Def_ModularCurve_JZeroNeronPrimaryTorsionSheaf
import P2M.Util
import P2M.Sol.S_ModularCurve_nonempty_jZeroNeronPrimaryTorsionFFModels
attribute [-instance] GaloisRep.ratLocalizedAt.span_isPrime GaloisRep.instAlgebraRatLocalizedAtZMod
open ModularCurve AlgebraicGeometry AlgebraicGeometry.Scheme ValuationSubring
theorem ModularCurve.nonempty_jZeroNeronPrimaryTorsionFFModels (p : ℕ) [Fact p.Prime] (q : ℕ) [Fact q.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (C : JZeroNeronPrimaryTorsionCore p q A hA) :
    Nonempty (JZeroNeronPrimaryTorsionFFModels p q A hA C) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_nonempty_jZeroNeronPrimaryTorsionFFModels.solution
