import Mathlib
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_GradedCartierModuleData_exists_mem_eta_nMap_eq_of_nMap_eq_nMap

set_option autoImplicit false

open CerednikDrinfeld

theorem CerednikDrinfeld.GradedCartierModuleData.exists_mem_eta_nMap_eq_of_nMap_eq_nMap
    (p : ℕ) [Fact p.Prime]
    {B B₀ B₁ B₀₁ : Type} [CommRing B] [CommRing B₀] [CommRing B₁] [CommRing B₀₁]
    {j : Zp2 p →+* B} {j₀ : Zp2 p →+* B₀} {j₁ : Zp2 p →+* B₁} {j₀₁ : Zp2 p →+* B₀₁}
    (D : GradedCartierModuleData p B j) (D₀ : GradedCartierModuleData p B₀ j₀)
    (D₁ : GradedCartierModuleData p B₁ j₁) (D₀₁ : GradedCartierModuleData p B₀₁ j₀₁)
    (f₀ : D.M →+ D₀.M) (f₁ : D.M →+ D₁.M) (g₀ : D₀.M →+ D₀₁.M) (g₁ : D₁.M →+ D₀₁.M)
    (hf₀V : ∀ m, f₀ (D.verschiebung m) = D₀.verschiebung (f₀ m)) (hf₀P : ∀ m, f₀ (D.varpi m) = D₀.varpi (f₀ m))
    (hf₁V : ∀ m, f₁ (D.verschiebung m) = D₁.verschiebung (f₁ m)) (hf₁P : ∀ m, f₁ (D.varpi m) = D₁.varpi (f₁ m))
    (hg₀V : ∀ m, g₀ (D₀.verschiebung m) = D₀₁.verschiebung (g₀ m)) (hg₀P : ∀ m, g₀ (D₀.varpi m) = D₀₁.varpi (g₀ m))
    (hg₁V : ∀ m, g₁ (D₁.verschiebung m) = D₀₁.verschiebung (g₁ m)) (hg₁P : ∀ m, g₁ (D₁.varpi m) = D₀₁.varpi (g₁ m))
    (hsq : ∀ m, g₀ (f₀ m) = g₁ (f₁ m))
    (hinj : ∀ m : D.M, f₀ m = 0 → f₁ m = 0 → m = 0)
    (hglue : ∀ (m₀ : D₀.M) (m₁ : D₁.M), g₀ m₀ = g₁ m₁ → ∃ m : D.M, f₀ m = m₀ ∧ f₁ m = m₁)
    (hg₀s : Function.Surjective g₀)
    (hV₀₁ : Function.Injective D₀₁.verschiebung)
    (L : D.M →+ D.NMod) (hL : D.IsCartierLMap L)
    (L₀ : D₀.M →+ D₀.NMod) (hL₀ : D₀.IsCartierLMap L₀)
    (L₁ : D₁.M →+ D₁.NMod) (hL₁ : D₁.IsCartierLMap L₁)
    (hLL₀ : ∀ m, L₀ (f₀ m) = D.nMap D₀ f₀ hf₀V hf₀P (L m))
    (hLL₁ : ∀ m, L₁ (f₁ m) = D.nMap D₁ f₁ hf₁V hf₁P (L m))
    (z₀ : D₀.NMod) (hz₀ : z₀ ∈ D₀.eta L₀ hL₀.map_verschiebung)
    (z₁ : D₁.NMod) (hz₁ : z₁ ∈ D₁.eta L₁ hL₁.map_verschiebung)
    (hcompat : D₀.nMap D₀₁ g₀ hg₀V hg₀P z₀ = D₁.nMap D₀₁ g₁ hg₁V hg₁P z₁) :
    ∃ z ∈ D.eta L hL.map_verschiebung,
      D.nMap D₀ f₀ hf₀V hf₀P z = z₀ ∧ D.nMap D₁ f₁ hf₁V hf₁P z = z₁ := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_GradedCartierModuleData_exists_mem_eta_nMap_eq_of_nMap_eq_nMap.solution
