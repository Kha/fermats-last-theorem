import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel
import Definitions.Def_CerednikDrinfeld_CartierQuadruple
import Definitions.Def_CerednikDrinfeld_PeriodMapSpec
import Definitions.Def_CerednikDrinfeld_SpecialFormalFunctorG
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_GradedCartierModuleData_eq_of_map_smul_of_map_verschiebung_of_forall_apply_basis_eq_of_isVAdicallyComplete

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic

theorem CerednikDrinfeld.GradedCartierModuleData.eq_of_map_smul_of_map_verschiebung_of_forall_apply_basis_eq_of_isVAdicallyComplete
    (p : ℕ) [Fact p.Prime] {R B' : Type} [CommRing R] [CommRing B']
    {jR : CerednikDrinfeld.Zp2 p →+* R} {j' : CerednikDrinfeld.Zp2 p →+* B'} (φ : R →+* B')
    (D : CerednikDrinfeld.GradedCartierModuleData p R jR)
    (D' : CerednikDrinfeld.GradedCartierModuleData p B' j') (hD' : D'.IsVAdicallyComplete)
    (γ : Fin 2 → D.M) (hγ : D.IsHomogeneousVBasis γ)
    (δ₁ δ₂ : D.M →+ D'.M)
    (h₁ : ∀ (w : WittVector p R) (x : D.M), δ₁ (w • x) = WittVector.map φ w • δ₁ x)
    (h₁V : ∀ x : D.M, δ₁ (D.verschiebung x) = D'.verschiebung (δ₁ x))
    (h₂ : ∀ (w : WittVector p R) (x : D.M), δ₂ (w • x) = WittVector.map φ w • δ₂ x)
    (h₂V : ∀ x : D.M, δ₂ (D.verschiebung x) = D'.verschiebung (δ₂ x))
    (hγeq : ∀ i : Fin 2, δ₁ (γ i) = δ₂ (γ i)) :
    δ₁ = δ₂ := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_GradedCartierModuleData_eq_of_map_smul_of_map_verschiebung_of_forall_apply_basis_eq_of_isVAdicallyComplete.solution
