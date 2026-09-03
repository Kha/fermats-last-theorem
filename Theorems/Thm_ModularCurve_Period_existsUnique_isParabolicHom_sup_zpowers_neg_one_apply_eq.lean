import Mathlib
import Definitions.Def_ModularCurve_PeriodMap
import P2M.Util
import P2M.Sol.S_ModularCurve_Period_existsUnique_isParabolicHom_sup_zpowers_neg_one_apply_eq

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.Period.existsUnique_isParabolicHom_sup_zpowers_neg_one_apply_eq
    (Γ : Subgroup SL(2, ℤ)) (A : Type*) [AddCommGroup A]
    (ψ : Additive Γ →+ A) (hψ : ModularCurve.Period.IsParabolicHom Γ ψ) :
    ∃! φ : Additive ↥(Γ ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))) →+ A,
      ModularCurve.Period.IsParabolicHom (Γ ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))) φ ∧
        ∀ γ : Γ, φ (Additive.ofMul ⟨(γ : SL(2, ℤ)), Subgroup.mem_sup_left γ.2⟩) = ψ (Additive.ofMul γ) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_Period_existsUnique_isParabolicHom_sup_zpowers_neg_one_apply_eq.solution
