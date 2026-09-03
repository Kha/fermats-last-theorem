import Definitions.Def_AutomorphicForm_TwistedOrbital
import P2M.Util
import P2M.Sol.S_AutomorphicForm_GL2Twisted_exists_isHaarMeasure_eq_smul_map_normSq_det_sq_inv
set_option autoImplicit false
open MeasureTheory
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.GL2Twisted.exists_isHaarMeasure_eq_smul_map_normSq_det_sq_inv
    (μ : @Measure (GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) (glBorelOf (ℂ ⊗[ℝ] ℝ)))
    (hμ : @Measure.IsHaarMeasure _ _ _ (glBorelOf (ℂ ⊗[ℝ] ℝ)) μ) :
    ∃ c : NNReal, 0 < c ∧
      μ = c • @Measure.map _ _ _ (glBorelOf (ℂ ⊗[ℝ] ℝ))
        (fun A : Fin 2 → Fin 2 → ℂ =>
          if h : (Matrix.of A).det ≠ 0 then
            Matrix.GeneralLinearGroup.map
              (@AlgEquiv.toRingEquiv ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _
                (Algebra.TensorProduct.rid ℝ ℝ ℂ)).symm.toRingHom
              (Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.of A) h)
          else 1)
        ((volume.restrict {A : Fin 2 → Fin 2 → ℂ | (Matrix.of A).det ≠ 0}).withDensity
          fun A => ENNReal.ofReal ((Complex.normSq (Matrix.of A).det ^ 2)⁻¹)) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_GL2Twisted_exists_isHaarMeasure_eq_smul_map_normSq_det_sq_inv.solution
