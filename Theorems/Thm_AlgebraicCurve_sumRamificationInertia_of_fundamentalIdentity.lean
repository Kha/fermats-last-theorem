import Definitions.Def_AlgebraicCurve_DivisorPushPull
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_sumRamificationInertia_of_fundamentalIdentity
open AlgebraicCurve

theorem AlgebraicCurve.sumRamificationInertia_of_fundamentalIdentity
    {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F']
    [IsScalarTower K F F'] [Algebra.IsIntegral F F'] [HasPrincipalDivisors K F']
    [FundamentalIdentity K F F']
    (hdeg : ∀ v : Place K F, v.deg ≠ 0) : SumRamificationInertia K F F' := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_sumRamificationInertia_of_fundamentalIdentity.solution
