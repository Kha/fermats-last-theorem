import Definitions.Def_ModularForm_HeckeOperator
import P2M.Util
namespace P2MW.S_ModularForm_coeffHeckeU_int

set_option autoImplicit false

open ModularForm

theorem solution (p : ℕ) {a : ℕ → ℂ} (ha : ∀ n : ℕ, ∃ m : ℤ, a n = m) (n : ℕ) : ∃ m : ℤ, ModularForm.coeffHeckeU p a n = m := by
  rw [coeffHeckeU_apply]
  exact ha (n * p)
