import Mathlib
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_GradedCartierModuleData_IsBaseChangeAlong_exists_eq_sum_teichmuller_smul_add_verschiebung_of_apply_eq_zero

set_option autoImplicit false

theorem CerednikDrinfeld.GradedCartierModuleData.IsBaseChangeAlong.exists_eq_sum_teichmuller_smul_add_verschiebung_of_apply_eq_zero
    (p : ℕ) [Fact p.Prime] {S B : Type} [CommRing S] [CommRing B]
    (jS : CerednikDrinfeld.Zp2 p →+* S) (φ : S →+* B)
    (Dl : CerednikDrinfeld.GradedCartierModuleData p S jS)
    (D : CerednikDrinfeld.GradedCartierModuleData p B (φ.comp jS))
    (f : Dl.M →+ D.M) (hf : CerednikDrinfeld.GradedCartierModuleData.IsBaseChangeAlong φ Dl D f)
    (γ : Fin 2 → Dl.M) (hγ : Dl.IsHomogeneousVBasis γ) (hγ' : D.IsHomogeneousVBasis (fun i => f (γ i)))
    (x : Dl.M) (hx : f x = 0) :
    ∃ (c : Fin 2 → S) (y : Dl.M), (∀ i, φ (c i) = 0) ∧ f y = 0 ∧
      x = (∑ i : Fin 2, WittVector.teichmuller p (c i) • γ i) + Dl.verschiebung y := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_GradedCartierModuleData_IsBaseChangeAlong_exists_eq_sum_teichmuller_smul_add_verschiebung_of_apply_eq_zero.solution
