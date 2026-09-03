import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_GL2RealOrbitalTransforms
import P2M.Util
import P2M.Sol.S_AutomorphicForm_GL2Real_orbitalIntegral_eq_splitTransform_div_and_eq_ellipticTransform_div

set_option autoImplicit false

open MeasureTheory AutomorphicForm AutomorphicForm.GL2Real

theorem AutomorphicForm.GL2Real.orbitalIntegral_eq_splitTransform_div_and_eq_ellipticTransform_div
    (f : GL (Fin 2) ℝ → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f)
    (μ : @Measure (GL (Fin 2) ℝ) (glBorelOf ℝ)) (hμ : @Measure.IsHaarMeasure _ _ _ (glBorelOf ℝ) μ) :
    (∀ (a₁ a₂ : ℝ) (h : a₁ * a₂ ≠ 0), a₁ ≠ a₂ →
      ∀ (τ : @Measure (Subgroup.centralizer ({upperTriangular a₁ a₂ 0 h} : Set (GL (Fin 2) ℝ)))
          (centralizerBorel ℝ (upperTriangular a₁ a₂ 0 h))),
        @Measure.IsHaarMeasure _ _ _ (centralizerBorel ℝ (upperTriangular a₁ a₂ 0 h)) τ →
        ∀ I : ℂ, IsOrbitalIntegralOn ℝ μ (upperTriangular a₁ a₂ 0 h) τ f I →
          I = (((μ {g | ∃ b₁ ∈ Set.Icc (1 : ℝ) (Real.exp 1), ∃ b₂ ∈ Set.Icc (1 : ℝ) (Real.exp 1),
                  ∃ x ∈ Set.Icc (0 : ℝ) 1, ∃ k : rowIsometrySubgroup₀ ℝ,
                  (g : Matrix (Fin 2) (Fin 2) ℝ) =
                    !![b₁, b₁ * x; 0, b₂] * ((k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)}).toReal /
                (τ {t | ((t : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 0 ∈ Set.Icc (1 : ℝ) (Real.exp 1) ∧
                  ((t : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 1 1 ∈ Set.Icc (1 : ℝ) (Real.exp 1)}).toReal :
                ℝ) : ℂ) *
              splitTransform f a₁ a₂ / ((2 * |a₁ - a₂| : ℝ) : ℂ)) ∧
    (∀ (r θ : ℝ) (hr : 0 < r), Real.sin θ ≠ 0 →
      ∀ (τ : @Measure (Subgroup.centralizer ({ellipticElt r θ hr} : Set (GL (Fin 2) ℝ)))
          (centralizerBorel ℝ (ellipticElt r θ hr))),
        @Measure.IsHaarMeasure _ _ _ (centralizerBorel ℝ (ellipticElt r θ hr)) τ →
        ∀ I : ℂ, IsOrbitalIntegralOn ℝ μ (ellipticElt r θ hr) τ f I →
          I = (((μ {g | ∃ b₁ ∈ Set.Icc (1 : ℝ) (Real.exp 1), ∃ b₂ ∈ Set.Icc (1 : ℝ) (Real.exp 1),
                  ∃ x ∈ Set.Icc (0 : ℝ) 1, ∃ k : rowIsometrySubgroup₀ ℝ,
                  (g : Matrix (Fin 2) (Fin 2) ℝ) =
                    !![b₁, b₁ * x; 0, b₂] * ((k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)}).toReal /
                (τ {t | Matrix.det ((t : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) ∈
                  Set.Icc (1 : ℝ) (Real.exp 2)}).toReal : ℝ) : ℂ) *
              ellipticTransform f r θ / (4 * Real.sin θ ^ 2 : ℂ)) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_GL2Real_orbitalIntegral_eq_splitTransform_div_and_eq_ellipticTransform_div.solution
