import Mathlib
import Definitions.Def_PadicComplex_TateTrace
import Definitions.Def_PadicAlgCl_CyclotomicTower
import P2M.Util
import P2M.Sol.S_PadicComplex_exists_isTateTrace_cyclotomicTower

set_option autoImplicit false

theorem PadicComplex.exists_isTateTrace_cyclotomicTower (p : ℕ) [Fact p.Prime] :
    ∃ d : ℝ, 0 < d ∧ ∀ m : ℕ, ∃ R : ℂ_[p] → ℂ_[p],
      PadicComplex.IsTateTrace p (fun n => PadicAlgCl.cyclotomicTower p (n + 2)) m d R := by p2m_exact_reverting @_root_.P2MW.S_PadicComplex_exists_isTateTrace_cyclotomicTower.solution
