import Definitions.Def_ModularForm_HeckeOperator
import P2M.Util
import P2M.Sol.S_ModularForm_coeffHeckeU_int

theorem ModularForm.coeffHeckeU_int (p : ℕ) {a : ℕ → ℂ} (ha : ∀ n : ℕ, ∃ m : ℤ, a n = m) (n : ℕ) : ∃ m : ℤ, ModularForm.coeffHeckeU p a n = m := by p2m_exact_reverting @_root_.P2MW.S_ModularForm_coeffHeckeU_int.solution
