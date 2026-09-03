import Mathlib
import Definitions.Def_ModularCurve_X1HeckeOperator
import Definitions.Def_ModularCurve_X1Diamond
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_algEquiv_intertwinesAlong_diamondAutBar
attribute [-instance] WeierstrassCurve.Affine.Point.instFinite
attribute [-simp] ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

theorem ModularCurve.exists_algEquiv_intertwinesAlong_diamondAutBar (M : ℕ) [NeZero M] (ℓ : ℕ)
    [NeZero ℓ] (d : ℕ) :
    ∃ τ : ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1x0FunctionFieldC ℚ M (M * ℓ))
        ≃ₐ[AlgebraicClosure ℚ]
        ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1x0FunctionFieldC ℚ M (M * ℓ)),
      AlgebraicCurve.SemilinearAut.IntertwinesAlong (ModularCurve.heckeAlphaOneBar (AlgebraicClosure ℚ) M ℓ).toRingHom
          (AlgebraicCurve.SemilinearAut.ofAlgAut (ModularCurve.diamondAutBar M d))
          (AlgebraicCurve.SemilinearAut.ofAlgAut τ) ∧
        AlgebraicCurve.SemilinearAut.IntertwinesAlong (ModularCurve.heckeBetaOneBar (AlgebraicClosure ℚ) M ℓ).toRingHom
          (AlgebraicCurve.SemilinearAut.ofAlgAut (ModularCurve.diamondAutBar M d))
          (AlgebraicCurve.SemilinearAut.ofAlgAut τ) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_algEquiv_intertwinesAlong_diamondAutBar.solution
