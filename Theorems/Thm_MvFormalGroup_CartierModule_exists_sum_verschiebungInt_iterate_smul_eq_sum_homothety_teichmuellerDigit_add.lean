import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleHomothety
import Definitions.Def_MvFormalGroup_CartierModuleWittAction
import Definitions.Def_MvFormalGroup_CartierModuleIntVerschiebung
import P2M.Util
import P2M.Sol.S_MvFormalGroup_CartierModule_exists_sum_verschiebungInt_iterate_smul_eq_sum_homothety_teichmuellerDigit_add

set_option autoImplicit false

universe u

theorem MvFormalGroup.CartierModule.exists_sum_verschiebungInt_iterate_smul_eq_sum_homothety_teichmuellerDigit_add
    (p : ℕ) [Fact p.Prime] {B : Type u} [CommRing B] {d : ℕ}
    (Φ : MvFormalGroup d B) [Φ.IsComm]
    (f : Fin d → MvFormalGroup.CartierModule p Φ)
    (c : ℕ → Fin d → Fin d → B)
    (h : ℕ → Fin d → MvFormalGroup.CartierModule p Φ)
    (hexp : ∀ (N : ℕ) (i : Fin d), MvFormalGroup.CartierModule.frobenius (f i) =
      (∑ m ∈ Finset.range N, (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ)))^[m]
          (∑ l : Fin d, MvFormalGroup.CartierModule.homothety (c m i l) (f l))) +
        (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ)))^[N] (h N i))
    (N : ℕ) (S : ℕ → Fin d → WittVector p B) :
    ∃ r : MvFormalGroup.CartierModule p Φ,
      (∑ m ∈ Finset.range N, (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ)))^[m]
          (∑ l : Fin d, S m l • f l)) =
      (∑ n ∈ Finset.range N, (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ)))^[n]
          (∑ l : Fin d, MvFormalGroup.CartierModule.homothety
            ((((fun T : ℕ → Fin d → WittVector p B => fun (m : ℕ) (l' : Fin d) =>
                  T (m + 1) l' + ∑ l : Fin d,
                    (⇑(WittVector.frobenius (p := p) (R := B)))^[m] ((T 0 l).shift 1) *
                      WittVector.teichmuller p (c m l l'))^[n] S) 0 l).coeff 0) (f l))) +
        (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ)))^[N] r := by p2m_exact_reverting @_root_.P2MW.S_MvFormalGroup_CartierModule_exists_sum_verschiebungInt_iterate_smul_eq_sum_homothety_teichmuellerDigit_add.solution
