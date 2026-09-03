import Mathlib
import Definitions.Def_ModularCurve_LevelNFunctionField
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff
import P2M.Util
import P2M.Sol.S_ModularCurve_LevelN_exists_algHom_laurentBaseChange_apply_eq_qExpand

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.LevelN.exists_algHom_laurentBaseChange_apply_eq_qExpand
    (M : ℕ) [NeZero M]
    (K : Type*) [Field K] [Algebra ℂ K] [Algebra (ModularCurve.LevelN.ring M) K]
    [IsScalarTower ℂ (ModularCurve.LevelN.ring M) K]
    [IsFractionRing (ModularCurve.LevelN.ring M) K]
    (σ : SL(2, ℤ) →* (K ≃ₐ[ℂ] K))
    (hker : σ.ker = CongruenceSubgroup.Gamma M ⊔ Subgroup.zpowers (-1 : SL(2, ℤ)))
    (hfixed : IntermediateField.fixedField σ.range =
      IntermediateField.adjoin ℂ
        ({algebraMap (ModularCurve.LevelN.ring M) K (ModularCurve.LevelN.jGen M)} : Set K))
    (E : K →ₐ[ℂ] LaurentSeries ℂ)
    (hEj : E (algebraMap (ModularCurve.LevelN.ring M) K (ModularCurve.LevelN.jGen M)) =
      ModularCurve.qExpand ℂ M (ModularCurve.jqModC ℂ))
    (Γ : Subgroup SL(2, ℤ)) (hΓ : CongruenceSubgroup.Gamma M ≤ Γ) (hT : ModularGroup.T ∈ Γ) :
    ∃ Ψ : ModularCurve.laurentBaseChange ℂ (ModularCurve.qExpFunctionFieldC ℚ Γ) →ₐ[ℂ] K,
      ∀ u : ModularCurve.laurentBaseChange ℂ (ModularCurve.qExpFunctionFieldC ℚ Γ),
        E (Ψ u) = ModularCurve.qExpand ℂ M (u : LaurentSeries ℂ) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_LevelN_exists_algHom_laurentBaseChange_apply_eq_qExpand.solution
