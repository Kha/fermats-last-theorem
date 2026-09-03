import Mathlib
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import P2M.Util
namespace P2MW.S_CerednikDrinfeld_GradedCartierModuleData_IsBaseChangeAlong_exists_eq_sum_teichmuller_smul_add_verschiebung_of_apply_eq_zero

set_option autoImplicit false

theorem solution
    (p : ℕ) [Fact p.Prime] {S B : Type} [CommRing S] [CommRing B]
    (jS : CerednikDrinfeld.Zp2 p →+* S) (φ : S →+* B)
    (Dl : CerednikDrinfeld.GradedCartierModuleData p S jS)
    (D : CerednikDrinfeld.GradedCartierModuleData p B (φ.comp jS))
    (f : Dl.M →+ D.M) (hf : CerednikDrinfeld.GradedCartierModuleData.IsBaseChangeAlong φ Dl D f)
    (γ : Fin 2 → Dl.M) (hγ : Dl.IsHomogeneousVBasis γ) (hγ' : D.IsHomogeneousVBasis (fun i => f (γ i)))
    (x : Dl.M) (hx : f x = 0) :
    ∃ (c : Fin 2 → S) (y : Dl.M), (∀ i, φ (c i) = 0) ∧ f y = 0 ∧
      x = (∑ i : Fin 2, WittVector.teichmuller p (c i) • γ i) + Dl.verschiebung y := by
  obtain ⟨⟨c, y⟩, hcy, -⟩ := hγ.2 x

  have himg : f x = (∑ i : Fin 2, WittVector.teichmuller p (φ (c i)) • f (γ i)) +
      D.verschiebung (f y) := by
    rw [hcy, map_add, map_sum, hf.2.2.1]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hf.1, WittVector.map_teichmuller]

  obtain ⟨cy', -, huniq⟩ := hγ'.2 (0 : D.M)
  have h1 : ((fun i => φ (c i)), f y) = cy' := by
    apply huniq
    show (0 : D.M) = (∑ i : Fin 2, WittVector.teichmuller p (φ (c i)) • f (γ i)) +
      D.verschiebung (f y)
    rw [← himg, hx]
  have h2 : ((fun _ => (0 : B)), (0 : D.M)) = cy' := by
    apply huniq
    show (0 : D.M) = (∑ i : Fin 2, WittVector.teichmuller p (0 : B) • f (γ i)) + D.verschiebung 0
    simp
  have h12 := h1.trans h2.symm
  have hc : (fun i => φ (c i)) = fun _ => (0 : B) := congrArg Prod.fst h12
  have hy : f y = 0 := congrArg Prod.snd h12
  exact ⟨c, y, fun i => congrFun hc i, hy, hcy⟩
