import Definitions.Def_AlgebraicCurve_DivisorPushPull
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Divisor_pushforward_pullback_of_finite

open AlgebraicCurve

theorem AlgebraicCurve.Divisor.pushforward_pullback_of_finite {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] [Algebra.IsIntegral F F'] [HasPrincipalDivisors K F'] [Module.Finite F F'] [SumRamificationInertia K F F'] (D : Divisor K F) : Divisor.pushforward F (Divisor.pullback F' D) = (Module.finrank F F' : ℤ) • D := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Divisor_pushforward_pullback_of_finite.solution
