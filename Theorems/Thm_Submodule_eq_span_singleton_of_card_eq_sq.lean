import Mathlib
import P2M.Util
import P2M.Sol.S_Submodule_eq_span_singleton_of_card_eq_sq

theorem Submodule.eq_span_singleton_of_card_eq_sq {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V] (hV : Nat.card V = p ^ 2) (N : Submodule (ZMod p) V) (htop : N ≠ ⊤) {v : V} (hv : v ∈ N) (hv0 : v ≠ 0) : N = Submodule.span (ZMod p) {v} := by p2m_exact_reverting @_root_.P2MW.S_Submodule_eq_span_singleton_of_card_eq_sq.solution
