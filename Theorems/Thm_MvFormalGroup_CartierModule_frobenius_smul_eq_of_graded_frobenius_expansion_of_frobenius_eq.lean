import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleHomothety
import Definitions.Def_MvFormalGroup_CartierModuleWittAction
import Definitions.Def_MvFormalGroup_CartierModuleIntVerschiebung
import P2M.Util
import P2M.Sol.S_MvFormalGroup_CartierModule_frobenius_smul_eq_of_graded_frobenius_expansion_of_frobenius_eq

set_option autoImplicit false

universe u

theorem MvFormalGroup.CartierModule.frobenius_smul_eq_of_graded_frobenius_expansion_of_frobenius_eq
    (p : ℕ) [Fact p.Prime] {B : Type u} [CommRing B]
    (Φ : MvFormalGroup 2 B) [Φ.IsComm]
    (f : Fin 2 → MvFormalGroup.CartierModule p Φ)
    (c : ℕ → Fin 2 → Fin 2 → B)
    (hc : ∀ (m : ℕ) (i l : Fin 2), (l : ℕ) ≠ (m + i + 1) % 2 → c m i l = 0)
    (h : ℕ → Fin 2 → MvFormalGroup.CartierModule p Φ)
    (hexp : ∀ (N : ℕ) (i : Fin 2), MvFormalGroup.CartierModule.frobenius (f i) =
      (∑ m ∈ Finset.range N, (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ)))^[m]
          (∑ l : Fin 2, MvFormalGroup.CartierModule.homothety (c m i l) (f l))) +
        (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ)))^[N] (h N i))
    (w : Fin 2 → WittVector p B)
    (hw : ∀ i : Fin 2, WittVector.frobenius (w i) = w (i + 1)) :
    ∀ (N : ℕ) (i : Fin 2), MvFormalGroup.CartierModule.frobenius (w i • f i) =
      (∑ m ∈ Finset.range N, (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ)))^[m]
          (∑ l : Fin 2, MvFormalGroup.CartierModule.homothety (c m i l) (w l • f l))) +
        (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ)))^[N]
          ((⇑(WittVector.frobenius (p := p) (R := B)))^[N + 1] (w i) • h N i) := by p2m_exact_reverting @_root_.P2MW.S_MvFormalGroup_CartierModule_frobenius_smul_eq_of_graded_frobenius_expansion_of_frobenius_eq.solution
