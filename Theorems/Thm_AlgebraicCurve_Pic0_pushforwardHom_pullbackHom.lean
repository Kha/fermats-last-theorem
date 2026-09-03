import Definitions.Def_AlgebraicCurve_DivisorPushPull
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Pic0_pushforwardHom_pullbackHom

open AlgebraicCurve
theorem AlgebraicCurve.Pic0.pushforwardHom_pullbackHom {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] [Algebra.IsIntegral F F'] [HasPrincipalDivisors K F'] [Module.Finite F F'] [SumRamificationInertia K F F'] (H : Divisor.PushforwardNormFormula K F F') (x : Pic0 K F) : Pic0.pushforwardHom K F F' H (Pic0.pullbackHom F' x) = (Module.finrank F F' : ℤ) • x := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Pic0_pushforwardHom_pullbackHom.solution
