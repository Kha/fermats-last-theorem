import Definitions.Def_ModularCurve_EisensteinTwoCoeff
import P2M.Util
import P2M.Sol.S_ModularCurve_eisensteinTwoCoeff_mul_level

open ModularCurve

theorem ModularCurve.eisensteinTwoCoeff_mul_level (p : ℕ) [Fact p.Prime] (n : ℕ) : eisensteinTwoCoeff p (n * p) = eisensteinTwoCoeff p n := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_eisensteinTwoCoeff_mul_level.solution
