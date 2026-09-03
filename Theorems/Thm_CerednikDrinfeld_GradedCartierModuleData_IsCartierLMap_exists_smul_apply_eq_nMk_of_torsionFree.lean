import Mathlib
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_GradedCartierModuleData_IsCartierLMap_exists_smul_apply_eq_nMk_of_torsionFree

set_option autoImplicit false

open CerednikDrinfeld

theorem CerednikDrinfeld.GradedCartierModuleData.IsCartierLMap.exists_smul_apply_eq_nMk_of_torsionFree
    (p : ℕ) [Fact p.Prime] {S : Type} [CommRing S] (jS : Zp2 p →+* S)
    (hS : ∀ s : S, (p : S) * s = 0 → s = 0)
    (D : GradedCartierModuleData p S jS) (γ : Fin 2 → D.M) (hγ : D.IsHomogeneousVBasis γ)
    (L : D.M →+ D.NMod) (hL : D.IsCartierLMap L) (i : Fin 2) :
    ∃ (a d : S) (x u v u' m : D.M) (ε : WittVector p S),
      D.varpi (γ i) = WittVector.teichmuller p a • γ (i + 1) + D.verschiebung x ∧
      ((p : ℕ) : WittVector p S) = WittVector.teichmuller p (p : S) + WittVector.verschiebung ε ∧
      ε • L (γ i) = D.nMk (x + u, v) ∧
      u = WittVector.teichmuller p (a ^ (p - 1) * d) • γ i + D.verschiebung u' ∧
      D.varpi u + D.verschiebung v = WittVector.teichmuller p a • m := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_GradedCartierModuleData_IsCartierLMap_exists_smul_apply_eq_nMk_of_torsionFree.solution
