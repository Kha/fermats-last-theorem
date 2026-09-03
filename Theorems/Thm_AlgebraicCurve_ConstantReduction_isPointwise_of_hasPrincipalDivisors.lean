import Definitions.Def_ModularCurve_FinitePlaceLift
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_ConstantReduction_isPointwise_of_hasPrincipalDivisors

open AlgebraicCurve
theorem AlgebraicCurve.ConstantReduction.isPointwise_of_hasPrincipalDivisors
    {K : Type*} [Field K] {A : ValuationSubring K} {F : Type*} [Field F] [Algebra K F]
    {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]
    [AlgebraicCurve.HasPrincipalDivisors K F] (R : AlgebraicCurve.ConstantReduction A F Fbar) :
    R.IsPointwise := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_ConstantReduction_isPointwise_of_hasPrincipalDivisors.solution
