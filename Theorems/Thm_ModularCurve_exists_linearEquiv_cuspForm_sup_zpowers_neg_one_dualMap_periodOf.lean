import Mathlib
import Definitions.Def_ModularCurve_PeriodOf
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_linearEquiv_cuspForm_sup_zpowers_neg_one_dualMap_periodOf

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.exists_linearEquiv_cuspForm_sup_zpowers_neg_one_dualMap_periodOf
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] :
    ∃ e : CuspForm ((Γ ⊔ Subgroup.zpowers (-1 : SL(2, ℤ)) : Subgroup SL(2, ℤ))) 2 ≃ₗ[ℂ] CuspForm Γ 2,
      (∀ f : CuspForm ((Γ ⊔ Subgroup.zpowers (-1 : SL(2, ℤ)) : Subgroup SL(2, ℤ))) 2, ∀ τ : UpperHalfPlane, e f τ = f τ) ∧
      (∀ g : CuspForm Γ 2, ∀ τ : UpperHalfPlane, e.symm g τ = g τ) ∧
      (∀ τ₀ τ₁ : UpperHalfPlane,
        e.toLinearMap.dualMap (ModularCurve.periodAlongOf Γ τ₀ τ₁) =
          ModularCurve.periodAlongOf (Γ ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))) τ₀ τ₁) ∧
      (∀ γ : Γ, e.toLinearMap.dualMap (ModularCurve.periodOf Γ γ) =
          ModularCurve.periodOf (Γ ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))) ⟨γ, Subgroup.mem_sup_left γ.2⟩) ∧
      (∀ (γ : SL(2, ℤ)) (h₁ : γ ∈ Γ ⊔ Subgroup.zpowers (-1 : SL(2, ℤ)))
          (h₂ : -γ ∈ Γ ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))),
        ModularCurve.periodOf (Γ ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))) ⟨-γ, h₂⟩ = ModularCurve.periodOf (Γ ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))) ⟨γ, h₁⟩) ∧
      (∀ φ : Module.Dual ℂ (CuspForm Γ 2),
        φ ∈ ModularCurve.periodLatticeOf Γ ↔
          e.toLinearMap.dualMap φ ∈ ModularCurve.periodLatticeOf (Γ ⊔ Subgroup.zpowers (-1 : SL(2, ℤ)))) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_linearEquiv_cuspForm_sup_zpowers_neg_one_dualMap_periodOf.solution
