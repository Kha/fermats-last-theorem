import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleHomothety
import Definitions.Def_MvFormalGroup_CartierModuleWittAction
import Definitions.Def_MvFormalGroup_CartierModuleIntVerschiebung
import Definitions.Def_MvFormalGroup_CartierModuleBaseChange
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_CartierGradedPiece
import Definitions.Def_CerednikDrinfeld_CartierStructureConstants
import P2M.Util
import P2M.Sol.S_MvFormalGroup_CartierModule_varpiTuple_rel_and_sum_eq_of_rel

set_option autoImplicit false

universe u

theorem MvFormalGroup.CartierModule.varpiTuple_rel_and_sum_eq_of_rel
    (p : ℕ) [Fact p.Prime] {B : Type u} [CommRing B]
    (a : ℕ → Fin 2 → B) (ha : a 0 0 * a 0 1 = (p : B))
    (Φ : MvFormalGroup 2 B) [Φ.IsComm]
    (f : Fin 2 → MvFormalGroup.CartierModule p Φ)
    (hrel : ∀ (N : ℕ) (i : Fin 2), ∃ s : MvFormalGroup.CartierModule p Φ,
      p • f i = WittVector.teichmuller p (p : B) • f i +
        (∑ k ∈ Finset.range N, (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ)))^[k + 1]
          ((∑ m ∈ Finset.range (k + 2), WittVector.teichmuller p
              (a m i ^ p ^ (k + 1 - m) * a (k + 1 - m) (CerednikDrinfeld.FormalODModule.piIndex m i))) •
            f (CerednikDrinfeld.FormalODModule.piIndex k i))) +
        (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ)))^[N + 1] s)
    (g : Fin 2 → MvFormalGroup.CartierModule p Φ)
    (r : ℕ → Fin 2 → MvFormalGroup.CartierModule p Φ)
    (hg : ∀ (N : ℕ) (i : Fin 2), g i =
      (∑ m ∈ Finset.range N, (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ)))^[m]
        (MvFormalGroup.CartierModule.homothety (a m i) (f (CerednikDrinfeld.FormalODModule.piIndex m i)))) +
      (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ)))^[N] (r N i)) :
    (∀ (N : ℕ) (i : Fin 2), ∃ s : MvFormalGroup.CartierModule p Φ,
      p • g i = WittVector.teichmuller p (p : B) • g i +
        (∑ k ∈ Finset.range N, (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ)))^[k + 1]
          ((∑ m ∈ Finset.range (k + 2), WittVector.teichmuller p
              (a m i ^ p ^ (k + 1 - m) * a (k + 1 - m) (CerednikDrinfeld.FormalODModule.piIndex m i))) •
            g (CerednikDrinfeld.FormalODModule.piIndex k i))) +
        (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ)))^[N + 1] s) ∧
    (∀ (N : ℕ) (i : Fin 2), ∃ s : MvFormalGroup.CartierModule p Φ,
      (∑ m ∈ Finset.range N, (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ)))^[m]
        (MvFormalGroup.CartierModule.homothety (a m i) (g (CerednikDrinfeld.FormalODModule.piIndex m i)))) +
      (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ)))^[N] s = p • f i) := by p2m_exact_reverting @_root_.P2MW.S_MvFormalGroup_CartierModule_varpiTuple_rel_and_sum_eq_of_rel.solution
