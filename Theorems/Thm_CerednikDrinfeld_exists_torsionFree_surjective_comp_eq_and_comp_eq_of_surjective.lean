import Mathlib
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_exists_torsionFree_surjective_comp_eq_and_comp_eq_of_surjective

set_option autoImplicit false

theorem CerednikDrinfeld.exists_torsionFree_surjective_comp_eq_and_comp_eq_of_surjective
    (p : ℕ) [Fact p.Prime] {S B : Type} [CommRing S] [CommRing B]
    (φ : S →+* B) (hφ : Function.Surjective φ) (hS : ∀ s : S, (p : S) * s = 0 → s = 0)
    (j : CerednikDrinfeld.Zp2 p →+* B) :
    ∃ (S' : Type) (_ : CommRing S') (ι : S →+* S') (j' : CerednikDrinfeld.Zp2 p →+* S') (q : S' →+* B),
      (∀ s : S', (p : S') * s = 0 → s = 0) ∧ Function.Surjective q ∧ q.comp ι = φ ∧ q.comp j' = j := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_exists_torsionFree_surjective_comp_eq_and_comp_eq_of_surjective.solution
