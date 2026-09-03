import Mathlib
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_hauptmodulFive_of_kernelQuadratic

theorem ModularCurve.exists_hauptmodulFive_of_kernelQuadratic (A B p q : ℚ) (hΔ : 4 * A ^ 3 + 27 * B ^ 2 ≠ 0) (hsep : p ^ 2 - 4 * q ≠ 0) (hg3 : 2 * A * p - 4 * B - p ^ 3 + 6 * p * q = 0) (hg4 : A ^ 2 - 2 * A * q + 4 * B * p - p ^ 2 * q + 5 * q ^ 2 = 0) : ∃ v : ℚ, v ≠ 0 ∧ (v ^ 2 + 10 * v + 5) ^ 3 * (-16 * (4 * A ^ 3 + 27 * B ^ 2)) = (-48 * A) ^ 3 * v := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_hauptmodulFive_of_kernelQuadratic.solution
