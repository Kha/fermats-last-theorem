import Definitions.Def_ModularCurve_X0
import P2M.Util
import P2M.Sol.S_ModularCurve_qExpand_linearIndependent_pow

set_option autoImplicit false

theorem ModularCurve.qExpand_linearIndependent_pow (κ : Type*) [Field κ] (q : ℕ) [Fact q.Prime] [CharP κ q]
    (j : LaurentSeries κ) (hj : j.coeff (-1) ≠ 0) (e : Fin q → LaurentSeries κ)
    (h : ∑ m, ModularCurve.qExpand κ q (e m) * j ^ (m : ℕ) = 0) : ∀ m, e m = 0 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_qExpand_linearIndependent_pow.solution
