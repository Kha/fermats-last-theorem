import Mathlib
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_GradedCartierModuleData_exists_dominating_of_apply_basis_eq

set_option autoImplicit false

theorem CerednikDrinfeld.GradedCartierModuleData.exists_dominating_of_apply_basis_eq
    (p : ℕ) [Fact p.Prime] {B S₁ S₂ : Type} [CommRing B] [CommRing S₁] [CommRing S₂]
    (j : CerednikDrinfeld.Zp2 p →+* B)
    (j₁ : CerednikDrinfeld.Zp2 p →+* S₁) (j₂ : CerednikDrinfeld.Zp2 p →+* S₂)
    (q₁ : S₁ →+* B) (q₂ : S₂ →+* B) (hq₁ : q₁.comp j₁ = j) (hq₂ : q₂.comp j₂ = j)
    (hS₁ : ∀ s : S₁, (p : S₁) * s = 0 → s = 0) (hS₂ : ∀ s : S₂, (p : S₂) * s = 0 → s = 0)
    (D : CerednikDrinfeld.GradedCartierModuleData p B j) (hD : D.IsSpecialCartierModule)
    (D₁ : CerednikDrinfeld.GradedCartierModuleData p S₁ j₁) (hD₁ : D₁.IsSpecialCartierModule)
    (D₂ : CerednikDrinfeld.GradedCartierModuleData p S₂ j₂) (hD₂ : D₂.IsSpecialCartierModule)
    (f₁ : D₁.M →+ D.M) (hf₁ : CerednikDrinfeld.GradedCartierModuleData.IsBaseChangeAlong' q₁ D₁ D f₁)
    (f₂ : D₂.M →+ D.M) (hf₂ : CerednikDrinfeld.GradedCartierModuleData.IsBaseChangeAlong' q₂ D₂ D f₂)
    (γ₁ : Fin 2 → D₁.M) (hγ₁ : D₁.IsHomogeneousVBasis γ₁)
    (γ₂ : Fin 2 → D₂.M) (hγ₂ : D₂.IsHomogeneousVBasis γ₂)
    (hγ : ∀ i : Fin 2, f₁ (γ₁ i) = f₂ (γ₂ i)) :
    ∃ (S₃ : Type) (_ : CommRing S₃) (j₃ : CerednikDrinfeld.Zp2 p →+* S₃) (r₁ : S₃ →+* S₁) (r₂ : S₃ →+* S₂)
      (_ : r₁.comp j₃ = j₁) (_ : r₂.comp j₃ = j₂) (_ : q₁.comp r₁ = q₂.comp r₂)
      (_ : ∀ s : S₃, (p : S₃) * s = 0 → s = 0)
      (D₃ : CerednikDrinfeld.GradedCartierModuleData p S₃ j₃) (_ : D₃.IsSpecialCartierModule)
      (γ₃ : Fin 2 → D₃.M) (_ : D₃.IsHomogeneousVBasis γ₃)
      (g₁ : D₃.M →+ D₁.M) (g₂ : D₃.M →+ D₂.M),
      CerednikDrinfeld.GradedCartierModuleData.IsBaseChangeAlong' r₁ D₃ D₁ g₁ ∧
        CerednikDrinfeld.GradedCartierModuleData.IsBaseChangeAlong' r₂ D₃ D₂ g₂ ∧
        (∀ i : Fin 2, g₁ (γ₃ i) = γ₁ i) ∧ (∀ i : Fin 2, g₂ (γ₃ i) = γ₂ i) ∧
        ∀ x : D₃.M, f₁ (g₁ x) = f₂ (g₂ x) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_GradedCartierModuleData_exists_dominating_of_apply_basis_eq.solution
