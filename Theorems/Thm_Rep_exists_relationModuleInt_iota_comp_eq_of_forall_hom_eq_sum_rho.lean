import Mathlib
import Definitions.Def_GroupCohomology_RelationModule
import P2M.Util
import P2M.Sol.S_Rep_exists_relationModuleInt_iota_comp_eq_of_forall_hom_eq_sum_rho

set_option autoImplicit false
open CategoryTheory

theorem Rep.exists_relationModuleInt_iota_comp_eq_of_forall_hom_eq_sum_rho
    {H : Type} [Group H] [Fintype H]
    (C : Rep ℤ H) (p : ℕ) [Fact p.Prime]
    (hnorm : ∀ c : C, ∃ d : C, (∀ g : H, C.ρ g d = d) ∧ (∑ g : H, C.ρ g c) = p • d)
    (B₀ : Rep ℤ H) [Fintype B₀] (hB₀ : ∀ b : B₀, p • b = 0) (htriv : ∀ (g : H) (b : B₀), B₀.ρ g b = b)
    (φ : Rep.relationModuleInt B₀ ⟶ C) (ψ : Rep.relationCarrier B₀ →+ C)
    (hφ : ∀ x : Rep.relationModuleInt B₀, φ.hom x = ∑ g : H, C.ρ g (ψ (Rep.relationRepInt B₀ g⁻¹ x))) :
    ∃ χ : Rep.free ℤ H B₀ ⟶ C, Rep.relationModuleInt.ι B₀ ≫ χ = φ := by p2m_exact_reverting @_root_.P2MW.S_Rep_exists_relationModuleInt_iota_comp_eq_of_forall_hom_eq_sum_rho.solution
