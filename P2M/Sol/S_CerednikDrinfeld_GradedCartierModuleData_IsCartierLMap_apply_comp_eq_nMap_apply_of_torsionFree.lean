import Mathlib
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Theorems.Thm_CerednikDrinfeld_GradedCartierModuleData_lambda_injective_of_isHomogeneousVBasis_of_torsionFree
import P2M.Util
namespace P2MW.S_CerednikDrinfeld_GradedCartierModuleData_IsCartierLMap_apply_comp_eq_nMap_apply_of_torsionFree

set_option autoImplicit false

theorem solution
    (p : ℕ) [Fact p.Prime] {S T : Type} [CommRing S] [CommRing T]
    {jS : CerednikDrinfeld.Zp2 p →+* S} {jT : CerednikDrinfeld.Zp2 p →+* T}
    (g : S →+* T) (hT : ∀ t : T, (p : T) * t = 0 → t = 0)
    (D : CerednikDrinfeld.GradedCartierModuleData p S jS) (hD : D.IsSpecialCartierModule)
    (D' : CerednikDrinfeld.GradedCartierModuleData p T jT) (hD' : D'.IsSpecialCartierModule)
    (f : D.M →+ D'.M) (hf : CerednikDrinfeld.GradedCartierModuleData.IsBaseChangeAlong' g D D' f)
    (L : D.M →+ D.NMod) (hL : D.IsCartierLMap L) (L' : D'.M →+ D'.NMod) (hL' : D'.IsCartierLMap L') :
    ∀ x : D.M, L' (f x) = D.nMap D' f hf.2.2.1 hf.2.2.2.1 (L x) := by
  intro x
  obtain ⟨γ', hγ'⟩ := hD'.1
  have hinj := CerednikDrinfeld.GradedCartierModuleData.lambda_injective_of_isHomogeneousVBasis_of_torsionFree
    p jT hT D' γ' hγ'
  apply hinj
  rw [hL'.lambda_comp, ← hf.2.1 x]
  obtain ⟨⟨m, m'⟩, hm⟩ := D.nMk_surjective (L x)
  rw [← hL.lambda_comp x, ← hm, CerednikDrinfeld.GradedCartierModuleData.nMap_nMk,
    CerednikDrinfeld.GradedCartierModuleData.lambda_nMk, CerednikDrinfeld.GradedCartierModuleData.lambda_nMk,
    map_add, hf.2.2.1, hf.2.2.2.1]
