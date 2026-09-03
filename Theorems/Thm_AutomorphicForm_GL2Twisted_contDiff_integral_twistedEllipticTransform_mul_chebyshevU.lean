import Definitions.Def_AutomorphicForm_GL2TwistedOrbitalTransforms
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.RingTheory.Polynomial.Chebyshev
import P2M.Util
import P2M.Sol.S_AutomorphicForm_GL2Twisted_contDiff_integral_twistedEllipticTransform_mul_chebyshevU

set_option autoImplicit false

open MeasureTheory Polynomial AutomorphicForm AutomorphicForm.GL2Twisted

theorem AutomorphicForm.GL2Twisted.contDiff_integral_twistedEllipticTransform_mul_chebyshevU
    (P : Type) [NormedAddCommGroup P] [NormedSpace ℝ P]
    (Φ : (Fin 2 → Fin 2 → ℂ) × P → ℂ) (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (hΦc : HasCompactSupport Φ)
    (hΦinv : tsupport Φ ⊆ {q | IsUnit (Matrix.det (Matrix.of q.1))}) (j : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × P => ∫ θ in (0 : ℝ)..Real.pi,
        twistedEllipticTransform (fun g => Φ (Matrix.of.symm (g : Matrix (Fin 2) (Fin 2) ℂ), q.2)) q.1 θ *
            (((Chebyshev.U ℝ (j : ℤ)).eval (Real.cos θ) : ℝ) : ℂ)) ∧
      HasCompactSupport (fun q : ℝ × P => ∫ θ in (0 : ℝ)..Real.pi,
        twistedEllipticTransform (fun g => Φ (Matrix.of.symm (g : Matrix (Fin 2) (Fin 2) ℂ), q.2)) q.1 θ *
            (((Chebyshev.U ℝ (j : ℤ)).eval (Real.cos θ) : ℝ) : ℂ)) ∧
      tsupport (fun q : ℝ × P => ∫ θ in (0 : ℝ)..Real.pi,
          twistedEllipticTransform (fun g => Φ (Matrix.of.symm (g : Matrix (Fin 2) (Fin 2) ℂ), q.2)) q.1 θ *
            (((Chebyshev.U ℝ (j : ℤ)).eval (Real.cos θ) : ℝ) : ℂ)) ⊆
        Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set P) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_GL2Twisted_contDiff_integral_twistedEllipticTransform_mul_chebyshevU.solution
