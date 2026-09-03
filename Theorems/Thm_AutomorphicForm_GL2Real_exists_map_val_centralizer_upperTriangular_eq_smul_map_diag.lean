import Definitions.Def_AutomorphicForm_GL2RealOrbitalTransforms
import Definitions.Def_AutomorphicForm_TwistedOrbital
import P2M.Util
import P2M.Sol.S_AutomorphicForm_GL2Real_exists_map_val_centralizer_upperTriangular_eq_smul_map_diag
set_option autoImplicit false
open MeasureTheory
open MeasureTheory AutomorphicForm AutomorphicForm.GL2Real

theorem
    AutomorphicForm.GL2Real.exists_map_val_centralizer_upperTriangular_eq_smul_map_diag
    (a₁ a₂ : ℝ) (h : a₁ * a₂ ≠ 0)
    (hne : a₁ ≠ a₂)
    (τ : @Measure (Subgroup.centralizer ({upperTriangular a₁ a₂ 0 h} : Set (GL (Fin 2) ℝ)))
      (centralizerBorel ℝ (upperTriangular a₁ a₂ 0 h)))
    (hτ : @Measure.IsHaarMeasure _ _ _ (centralizerBorel ℝ (upperTriangular a₁ a₂ 0 h)) τ) :
    ∃ c : NNReal, 0 < c ∧
      @Measure.map _ _ (centralizerBorel ℝ (upperTriangular a₁ a₂ 0 h)) (glBorelOf ℝ) Subtype.val τ =
        c • @Measure.map (ℝ × ℝ) _ _ (glBorelOf ℝ)
          (fun α : ℝ × ℝ => if hα : α.1 * α.2 ≠ 0 then upperTriangular α.1 α.2 0 hα else 1)
          ((volume.restrict {α : ℝ × ℝ | α.1 * α.2 ≠ 0}).withDensity
            (fun α => ENNReal.ofReal |α.1 * α.2|⁻¹)) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_GL2Real_exists_map_val_centralizer_upperTriangular_eq_smul_map_diag.solution
