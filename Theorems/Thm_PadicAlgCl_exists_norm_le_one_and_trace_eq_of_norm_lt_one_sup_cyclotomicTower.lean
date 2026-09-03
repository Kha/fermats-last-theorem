import Mathlib
import Definitions.Def_PadicAlgCl_CyclotomicTower
import P2M.Util
import P2M.Sol.S_PadicAlgCl_exists_norm_le_one_and_trace_eq_of_norm_lt_one_sup_cyclotomicTower

set_option autoImplicit false

theorem PadicAlgCl.exists_norm_le_one_and_trace_eq_of_norm_lt_one_sup_cyclotomicTower
    (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
    (L : IntermediateField ↥(K ⊔ ⨆ n : ℕ, PadicAlgCl.cyclotomicTower p n) (PadicAlgCl p))
    [FiniteDimensional ↥(K ⊔ ⨆ n : ℕ, PadicAlgCl.cyclotomicTower p n) L]
    (x : ↥(K ⊔ ⨆ n : ℕ, PadicAlgCl.cyclotomicTower p n)) (hx : ‖(x : PadicAlgCl p)‖ < 1) :
    ∃ y : L, ‖(y : PadicAlgCl p)‖ ≤ 1 ∧
      Algebra.trace ↥(K ⊔ ⨆ n : ℕ, PadicAlgCl.cyclotomicTower p n) L y = x := by p2m_exact_reverting @_root_.P2MW.S_PadicAlgCl_exists_norm_le_one_and_trace_eq_of_norm_lt_one_sup_cyclotomicTower.solution
