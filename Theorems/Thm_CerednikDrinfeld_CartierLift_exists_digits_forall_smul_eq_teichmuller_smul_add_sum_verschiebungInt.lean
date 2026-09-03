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
import P2M.Sol.S_CerednikDrinfeld_CartierLift_exists_digits_forall_smul_eq_teichmuller_smul_add_sum_verschiebungInt

set_option autoImplicit false

theorem CerednikDrinfeld.CartierLift.exists_digits_forall_smul_eq_teichmuller_smul_add_sum_verschiebungInt
    (p : ℕ) [Fact p.Prime] :
    ∃ C : ℕ → Fin 2 → Fin 2 →
        CerednikDrinfeld.CartierLift.LiftRing p (CerednikDrinfeld.Zp2 p) ((0, 0) : ℕ × Fin 2) (0, 1),
      (∀ (m : ℕ) (i l : Fin 2), (l : ℕ) ≠ (m + i + 1) % 2 → C m i l = 0) ∧
      ∀ (Φ : MvFormalGroup 2
            (CerednikDrinfeld.CartierLift.LiftRing p (CerednikDrinfeld.Zp2 p) ((0, 0) : ℕ × Fin 2) (0, 1)))
        [Φ.IsComm]
        (f : Fin 2 → MvFormalGroup.CartierModule p Φ)
        (_hf : ∀ i l, MvFormalGroup.CartierModule.tangent (f i) l = if i = l then 1 else 0)
        (h : ℕ → Fin 2 → MvFormalGroup.CartierModule p Φ)
        (_hexp : ∀ (N : ℕ) (i : Fin 2), MvFormalGroup.CartierModule.frobenius (f i) =
          (∑ m ∈ Finset.range N, (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ)))^[m]
              (∑ l : Fin 2, MvFormalGroup.CartierModule.homothety (C m i l) (f l))) +
            (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ)))^[N] (h N i))
        (N : ℕ) (i : Fin 2),
        ∃ s : MvFormalGroup.CartierModule p Φ,
          p • f i =
            WittVector.teichmuller p
                (p : CerednikDrinfeld.CartierLift.LiftRing p (CerednikDrinfeld.Zp2 p) ((0, 0) : ℕ × Fin 2) (0, 1)) •
              f i +
            (∑ k ∈ Finset.range N,
              (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ)))^[k + 1]
                ((∑ m ∈ Finset.range (k + 2),
                    WittVector.teichmuller p
                      (CerednikDrinfeld.CartierLift.liftVar (p := p) (R := CerednikDrinfeld.Zp2 p)
                          ((0, 0) : ℕ × Fin 2) (0, 1) (m, i) ^ p ^ (k + 1 - m) *
                        CerednikDrinfeld.CartierLift.liftVar (p := p) (R := CerednikDrinfeld.Zp2 p)
                          ((0, 0) : ℕ × Fin 2) (0, 1)
                          (k + 1 - m, CerednikDrinfeld.FormalODModule.piIndex m i))) •
                  f (CerednikDrinfeld.FormalODModule.piIndex k i))) +
            (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ)))^[N + 1] s := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_CartierLift_exists_digits_forall_smul_eq_teichmuller_smul_add_sum_verschiebungInt.solution
