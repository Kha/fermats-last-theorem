import Mathlib
import P2M.Util
import P2M.Sol.S_WittVector_exists_eq_sum_iterate_verschiebung_teichmuller_add

set_option autoImplicit false

theorem WittVector.exists_eq_sum_iterate_verschiebung_teichmuller_add
    (p : ℕ) [Fact p.Prime] {B : Type} [CommRing B] (w : WittVector p B) (N : ℕ) :
    ∃ w' : WittVector p B,
      w = (∑ n ∈ Finset.range N, (⇑(WittVector.verschiebung : WittVector p B →+ WittVector p B))^[n]
            (WittVector.teichmuller p (w.coeff n))) +
          (⇑(WittVector.verschiebung : WittVector p B →+ WittVector p B))^[N] w' := by p2m_exact_reverting @_root_.P2MW.S_WittVector_exists_eq_sum_iterate_verschiebung_teichmuller_add.solution
