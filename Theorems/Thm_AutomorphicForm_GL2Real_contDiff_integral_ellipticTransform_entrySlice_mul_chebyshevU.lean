import Definitions.Def_AutomorphicForm_GL2RealOrbitalTransforms
import P2M.Util
import P2M.Sol.S_AutomorphicForm_GL2Real_contDiff_integral_ellipticTransform_entrySlice_mul_chebyshevU

set_option autoImplicit false

open MeasureTheory Polynomial AutomorphicForm AutomorphicForm.GL2Real

theorem AutomorphicForm.GL2Real.contDiff_integral_ellipticTransform_entrySlice_mul_chebyshevU
    (P : Type) [NormedAddCommGroup P] [NormedSpace ℝ P]
    (Φ : (Fin 2 → Fin 2 → ℝ) × P → ℂ) (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (hΦc : HasCompactSupport Φ)
    (hΦinv : tsupport Φ ⊆ {q | IsUnit (Matrix.det (Matrix.of q.1))}) (j : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × P => ∫ θ in (0 : ℝ)..Real.pi,
        ellipticTransform (entrySlice Φ q.2) q.1 θ * (((Chebyshev.U ℝ (j : ℤ)).eval (Real.cos θ) : ℝ) : ℂ)) ∧
      HasCompactSupport (fun q : ℝ × P => ∫ θ in (0 : ℝ)..Real.pi,
        ellipticTransform (entrySlice Φ q.2) q.1 θ * (((Chebyshev.U ℝ (j : ℤ)).eval (Real.cos θ) : ℝ) : ℂ)) ∧
      tsupport (fun q : ℝ × P => ∫ θ in (0 : ℝ)..Real.pi,
          ellipticTransform (entrySlice Φ q.2) q.1 θ * (((Chebyshev.U ℝ (j : ℤ)).eval (Real.cos θ) : ℝ) : ℂ)) ⊆
        Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set P) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_GL2Real_contDiff_integral_ellipticTransform_entrySlice_mul_chebyshevU.solution
