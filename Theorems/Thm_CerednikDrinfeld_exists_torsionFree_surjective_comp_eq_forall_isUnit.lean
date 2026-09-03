import Mathlib
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_exists_torsionFree_surjective_comp_eq_forall_isUnit

set_option autoImplicit false

theorem CerednikDrinfeld.exists_torsionFree_surjective_comp_eq_forall_isUnit
    (p : ℕ) {S B : Type} [CommRing S] [CommRing B]
    (q : S →+* B) (hq : Function.Surjective q) (hS : ∀ s : S, (p : S) * s = 0 → s = 0) :
    ∃ (S' : Type) (_ : CommRing S') (ι : S →+* S') (q' : S' →+* B),
      (∀ s : S', (p : S') * s = 0 → s = 0) ∧ Function.Surjective q' ∧ q'.comp ι = q ∧
      ∀ s : S', IsUnit (q' s) → IsUnit s := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_exists_torsionFree_surjective_comp_eq_forall_isUnit.solution
