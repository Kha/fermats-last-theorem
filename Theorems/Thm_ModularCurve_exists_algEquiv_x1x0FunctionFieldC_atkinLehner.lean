import Mathlib
import Definitions.Def_ModularCurve_X1HeckeOperator
import Definitions.Def_ModularCurve_X1Diamond
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_algEquiv_x1x0FunctionFieldC_atkinLehner
attribute [-instance] WeierstrassCurve.Affine.Point.instFinite
attribute [-simp] ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

theorem ModularCurve.exists_algEquiv_x1x0FunctionFieldC_atkinLehner
    (M : ℕ) [NeZero M] (ℓ : ℕ) [Fact ℓ.Prime] (hℓM : ¬ ℓ ∣ M)
    (hβ : ModularCurve.HeckeBetaOneDefined M ℓ)
    (hσ : ∃ σ : ↥(ModularCurve.x1FunctionField M) ≃ₐ[ℚ] ↥(ModularCurve.x1FunctionField M),
      ModularCurve.IsDiamondAut M ℓ σ)
    (hσ' : ∃ σ' : ↥(ModularCurve.x1FunctionFieldBar M) ≃ₐ[AlgebraicClosure ℚ]
        ↥(ModularCurve.x1FunctionFieldBar M),
      ModularCurve.IsBaseChangeAutOf (AlgebraicClosure ℚ) (ModularCurve.diamondAut M ℓ) σ') :
    ∃ W : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
            (ModularCurve.x1x0FunctionFieldC ℚ M (M * ℓ))) ≃ₐ[AlgebraicClosure ℚ]
        ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
            (ModularCurve.x1x0FunctionFieldC ℚ M (M * ℓ))),
      (∀ x : ↥(ModularCurve.x1FunctionFieldBar M),
        W (ModularCurve.heckeBetaOneBar (AlgebraicClosure ℚ) M ℓ x) =
          ModularCurve.heckeAlphaOneBar (AlgebraicClosure ℚ) M ℓ x) ∧
      ∀ x : ↥(ModularCurve.x1FunctionFieldBar M),
        W (ModularCurve.heckeAlphaOneBar (AlgebraicClosure ℚ) M ℓ x) =
          ModularCurve.heckeBetaOneBar (AlgebraicClosure ℚ) M ℓ
            ((ModularCurve.diamondAutBar M ℓ).symm x) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_algEquiv_x1x0FunctionFieldC_atkinLehner.solution
