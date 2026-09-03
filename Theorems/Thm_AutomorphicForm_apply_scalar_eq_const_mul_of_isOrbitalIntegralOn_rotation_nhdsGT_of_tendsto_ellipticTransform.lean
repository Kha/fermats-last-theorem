import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_GL2RealOrbitalTransforms
import P2M.Util
import P2M.Sol.S_AutomorphicForm_apply_scalar_eq_const_mul_of_isOrbitalIntegralOn_rotation_nhdsGT_of_tendsto_ellipticTransform

set_option autoImplicit false

open MeasureTheory AutomorphicForm AutomorphicForm.GL2Real
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.apply_scalar_eq_const_mul_of_isOrbitalIntegralOn_rotation_nhdsGT_of_tendsto_ellipticTransform
    (μ : @Measure (GL (Fin 2) ℝ) (glBorelOf ℝ))
    (hμ : @Measure.IsHaarMeasure _ _ _ (glBorelOf ℝ) μ)
    (c : ℝˣ)
    (γ : ℝ → GL (Fin 2) ℝ)
    (hγ : ∀ θ : ℝ, ((γ θ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      (c : ℝ) • !![Real.cos θ, -Real.sin θ; Real.sin θ, Real.cos θ])
    (νT : @Measure (GL (Fin 2) ℝ) (glBorelOf ℝ))
    (C : ℝ) (hC : C ≠ 0)
    (hjump : ∀ (P : Type) [NormedAddCommGroup P] [NormedSpace ℝ P] (Φ : (Fin 2 → Fin 2 → ℝ) × P → ℂ),
        ContDiff ℝ (⊤ : ℕ∞) Φ → HasCompactSupport Φ →
        tsupport Φ ⊆ {q | IsUnit (Matrix.det (Matrix.of q.1))} →
        ∀ (p : P) (r : ℝ), 0 < r →
          ∃ L : ℂ,
            Filter.Tendsto (fun θ : ℝ => ellipticTransform (entrySlice Φ p) r θ / (2 * Real.sin θ : ℂ))
              (nhdsWithin 0 (Set.Ioi 0)) (nhds L) ∧
            Filter.Tendsto
              (fun θ : ℝ => (ellipticTransform (entrySlice Φ p) r θ / (2 * Real.sin θ : ℂ) - L) / (θ : ℂ))
              (nhdsWithin 0 (Set.Ioi 0))
              (nhds ((C : ℂ) * Φ (Matrix.of.symm (r • (1 : Matrix (Fin 2) (Fin 2) ℝ)), p)))) :
      ∀ (f : GL (Fin 2) ℝ → ℂ),
        ((∃ F : (Fin 2 → Fin 2 → ℝ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) F ∧
          ∀ g, f g = F (fun i j => (g : Matrix (Fin 2) (Fin 2) ℝ) i j)) ∧ HasCompactSupport f) →
      ∀ (θ₀ : ℝ), 0 < θ₀ →
      ∀ (τ : ∀ θ : ℝ, @Measure (Subgroup.centralizer ({γ θ} : Set (GL (Fin 2) ℝ))) (centralizerBorel ℝ (γ θ))),
        (∀ θ ∈ Set.Ioo 0 θ₀, @Measure.IsHaarMeasure _ _ _ (centralizerBorel ℝ (γ θ)) (τ θ)) →
        (∀ θ ∈ Set.Ioo 0 θ₀, @Measure.map _ _ (centralizerBorel ℝ (γ θ)) (glBorelOf ℝ) Subtype.val (τ θ) = νT) →
      ∀ (Φ : ℝ → ℂ),
        (∀ θ ∈ Set.Ioo 0 θ₀, IsOrbitalIntegralOn ℝ μ (γ θ) (τ θ) f (Φ θ)) →
        ∃ L₁ L₂ : ℂ,
          Filter.Tendsto (fun θ : ℝ => (Real.sin θ : ℂ) * Φ θ) (nhdsWithin 0 (Set.Ioi 0)) (nhds L₁) ∧
          Filter.Tendsto (fun θ : ℝ => ((Real.sin θ : ℂ) * Φ θ - L₁) / (θ : ℂ)) (nhdsWithin 0 (Set.Ioi 0))
            (nhds L₂) ∧
          0 < (νT {g : GL (Fin 2) ℝ | Matrix.det (g : Matrix (Fin 2) (Fin 2) ℝ) ∈ Set.Icc (1 : ℝ) (Real.exp 2)}).toReal ∧
          f (Matrix.GeneralLinearGroup.scalar (Fin 2) c) =
            (((2 : ℝ) /
                ((μ {g : GL (Fin 2) ℝ | ∃ b₁ ∈ Set.Icc (1 : ℝ) (Real.exp 1), ∃ b₂ ∈ Set.Icc (1 : ℝ) (Real.exp 1),
              ∃ x ∈ Set.Icc (0 : ℝ) 1, ∃ k : rowIsometrySubgroup₀ ℝ,
              (g : Matrix (Fin 2) (Fin 2) ℝ) =
                !![b₁, b₁ * x; 0, b₂] * ((k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)}).toReal /
                    (νT {g : GL (Fin 2) ℝ | Matrix.det (g : Matrix (Fin 2) (Fin 2) ℝ) ∈ Set.Icc (1 : ℝ) (Real.exp 2)}).toReal *
                  C) : ℝ) : ℂ) * L₂ := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_apply_scalar_eq_const_mul_of_isOrbitalIntegralOn_rotation_nhdsGT_of_tendsto_ellipticTransform.solution
