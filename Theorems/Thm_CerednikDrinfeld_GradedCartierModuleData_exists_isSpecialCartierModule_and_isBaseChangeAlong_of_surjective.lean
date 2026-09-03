import Mathlib
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_GradedCartierModuleData_exists_isSpecialCartierModule_and_isBaseChangeAlong_of_surjective

set_option autoImplicit false

theorem CerednikDrinfeld.GradedCartierModuleData.exists_isSpecialCartierModule_and_isBaseChangeAlong_of_surjective
    (p : ℕ) [Fact p.Prime] {B C : Type} [CommRing B] [CommRing C]
    (j : CerednikDrinfeld.Zp2 p →+* B) (ψ : B →+* C) (hψ : Function.Surjective ψ)
    (D : CerednikDrinfeld.GradedCartierModuleData p B j) (hD : D.IsSpecialCartierModule) :
    ∃ (D₁ : CerednikDrinfeld.GradedCartierModuleData p C (ψ.comp j)) (g : D.M →+ D₁.M),
      D₁.IsSpecialCartierModule ∧
      CerednikDrinfeld.GradedCartierModuleData.IsBaseChangeAlong ψ D D₁ g ∧
      ∀ γ : Fin 2 → D.M, D.IsHomogeneousVBasis γ → D₁.IsHomogeneousVBasis (fun i => g (γ i)) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_GradedCartierModuleData_exists_isSpecialCartierModule_and_isBaseChangeAlong_of_surjective.solution
