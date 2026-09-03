import Definitions.Def_ModularCurve_EichlerShimuraData
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_Repartitions
import P2M.Util
import P2M.Sol.S_ModularCurve_JZero_finite_torsion_pow_of_cardinalityAJ

open AlgebraicCurve ModularCurve

theorem ModularCurve.JZero.finite_torsion_pow_of_cardinalityAJ (N : ℕ) [NeZero N] (p : ℕ) [Fact p.Prime]
    (hK1 : CardinalityAJ p (JZero N) (genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N)))
    (k : ℕ) : Finite (Pic0.torsion (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (p ^ k)) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_JZero_finite_torsion_pow_of_cardinalityAJ.solution
