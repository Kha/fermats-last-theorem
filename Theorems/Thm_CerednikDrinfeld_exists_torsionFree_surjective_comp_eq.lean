import Mathlib
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_exists_torsionFree_surjective_comp_eq

set_option autoImplicit false

theorem CerednikDrinfeld.exists_torsionFree_surjective_comp_eq
    (p : ℕ) {S B : Type} [CommRing S] [CommRing B] (h : S →+* B) (hS : ∀ s : S, (p : S) * s = 0 → s = 0) :
    ∃ (T : Type) (_ : CommRing T) (i : S →+* T) (q : T →+* B),
      (∀ t : T, (p : T) * t = 0 → t = 0) ∧ Function.Surjective q ∧ q.comp i = h := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_exists_torsionFree_surjective_comp_eq.solution
