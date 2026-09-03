import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_exists_isQuadraticDatum_of_sq_lt_four_mul_of_not_isSquare_padic

set_option autoImplicit false

open scoped Quaternion

theorem QuaternionAlgebra.exists_isQuadraticDatum_of_sq_lt_four_mul_of_not_isSquare_padic
    {a b : ℚ} (p : ℕ) [Fact p.Prime] (hdef : QuaternionAlgebra.IsDefiniteRamifiedExactlyAt a b p)
    (t n : ℤ) (hneg : t ^ 2 < 4 * n) (hp : ¬ IsSquare ((t ^ 2 - 4 * n : ℤ) : ℚ_[p])) :
    ∃ β : ℍ[ℚ, a, b], QuaternionAlgebra.IsQuadraticDatum t n β := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_exists_isQuadraticDatum_of_sq_lt_four_mul_of_not_isSquare_padic.solution
