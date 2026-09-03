import Mathlib
import Definitions.Def_ModularForm_HeckeOperatorForms
import P2M.Util
import P2M.Sol.S_ModularForm_heckeTLin_comm

theorem ModularForm.heckeTLin_comm {N : ℕ} (k : ℤ) {p q : ℕ} (hp : p.Prime) (hpN : ¬ p ∣ N) (hq : q.Prime) (hqN : ¬ q ∣ N) :
    Commute (ModularForm.heckeTLin k hp hpN) (ModularForm.heckeTLin k hq hqN) := by p2m_exact_reverting @_root_.P2MW.S_ModularForm_heckeTLin_comm.solution
