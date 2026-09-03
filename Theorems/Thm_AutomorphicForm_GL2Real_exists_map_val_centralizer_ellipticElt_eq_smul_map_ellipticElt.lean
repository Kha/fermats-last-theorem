import Definitions.Def_AutomorphicForm_GL2RealOrbitalTransforms
import Definitions.Def_AutomorphicForm_TwistedOrbital
import P2M.Util
import P2M.Sol.S_AutomorphicForm_GL2Real_exists_map_val_centralizer_ellipticElt_eq_smul_map_ellipticElt
set_option autoImplicit false
open MeasureTheory
open MeasureTheory AutomorphicForm AutomorphicForm.GL2Real

theorem AutomorphicForm.GL2Real.exists_map_val_centralizer_ellipticElt_eq_smul_map_ellipticElt (r θ : ℝ) (hr : 0 < r)
    (hθ : Real.sin θ ≠ 0)
    (τ : @Measure (Subgroup.centralizer ({ellipticElt r θ hr} : Set (GL (Fin 2) ℝ)))
      (centralizerBorel ℝ (ellipticElt r θ hr)))
    (hτ : @Measure.IsHaarMeasure _ _ _ (centralizerBorel ℝ (ellipticElt r θ hr)) τ) :
    ∃ c : NNReal, 0 < c ∧
      @Measure.map _ _ (centralizerBorel ℝ (ellipticElt r θ hr)) (glBorelOf ℝ) Subtype.val τ =
        c • @Measure.map (ℝ × ℝ) _ _ (glBorelOf ℝ)
          (fun q : ℝ × ℝ => if hq : 0 < q.1 then ellipticElt q.1 q.2 hq else 1)
          ((volume.restrict (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (2 * Real.pi))).withDensity
            (fun q => ENNReal.ofReal q.1⁻¹)) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_GL2Real_exists_map_val_centralizer_ellipticElt_eq_smul_map_ellipticElt.solution
