import Mathlib
import Definitions.Def_ModularCurve_X1
import P2M.Util
import P2M.Sol.S_ModularCurve_qExpand_image_intFormRatiosC_subset
attribute [-instance] WeierstrassCurve.Affine.Point.instFinite
attribute [-simp] ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

open scoped MatrixGroups in

theorem ModularCurve.qExpand_image_intFormRatiosC_subset (K : Type*) [Field K]
    {Γ Γ' : Subgroup SL(2, ℤ)} [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ) (ℓ : ℕ) [NeZero ℓ]
    (hΓ' : ∀ γ ∈ Γ', ∃ γ₁ ∈ Γ,
      γ₁ 0 0 = γ 0 0 ∧ γ₁ 0 1 = (ℓ : ℤ) * γ 0 1 ∧ (ℓ : ℤ) * γ₁ 1 0 = γ 1 0 ∧ γ₁ 1 1 = γ 1 1) :
    ModularCurve.qExpand K ℓ '' ModularCurve.intFormRatiosC K Γ ⊆
      ModularCurve.intFormRatiosC K Γ' := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_qExpand_image_intFormRatiosC_subset.solution
