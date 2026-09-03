import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_GL2TwistedOrbitalTransforms
import P2M.Util
import P2M.Sol.S_AutomorphicForm_GL2Twisted_twistedOrbitalIntegral_eq_twistedSplitTransform_div_and_eq_twistedEllipticTransform_div

set_option autoImplicit false

open MeasureTheory AutomorphicForm AutomorphicForm.GL2Twisted
open scoped TensorProduct TensorProduct.RightActions

theorem
AutomorphicForm.GL2Twisted.twistedOrbitalIntegral_eq_twistedSplitTransform_div_and_eq_twistedEllipticTransform_div
    (φ : GL (Fin 2) ℂ → ℂ) (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (μ : @Measure (GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) (glBorelOf (ℂ ⊗[ℝ] ℝ)))
    (hμ : @Measure.IsHaarMeasure _ _ _ (glBorelOf (ℂ ⊗[ℝ] ℝ)) μ) :
    (∀ (a₁ a₂ : ℝ), 0 < a₁ → 0 < a₂ → a₁ ≠ a₂ →
      ∀ δ : GL (Fin 2) (ℂ ⊗[ℝ] ℝ),
        ((Matrix.GeneralLinearGroup.map
          (@AlgEquiv.toRingEquiv ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _
            (Algebra.TensorProduct.rid ℝ ℝ ℂ)).toRingHom
          δ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
          !![((Real.sqrt a₁ : ℝ) : ℂ), 0; 0, ((Real.sqrt a₂ : ℝ) : ℂ)] →
        ∀ (τ : @Measure (twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ)
            (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ)),
          @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ) τ →
          ∀ I : ℂ,
            IsTwistedOrbitalIntegralOn ℝ ℂ ℝ Complex.conjAe μ δ τ
              (fun y => φ
                (Matrix.GeneralLinearGroup.map
                  (@AlgEquiv.toRingEquiv ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _
                    (Algebra.TensorProduct.rid ℝ ℝ ℂ)).toRingHom y : GL (Fin 2) ℂ)) I →
            I = (((
              (μ {g | ∃ b₁ ∈ Set.Icc (1 : ℝ) (Real.exp 1), ∃ b₂ ∈ Set.Icc (1 : ℝ) (Real.exp 1),
                  ∃ v : ℂ, v.re ∈ Set.Icc (0 : ℝ) 1 ∧ v.im ∈ Set.Icc (0 : ℝ) 1 ∧
                  ∃ k : AutomorphicForm.WindowedSiegel.rowIsometrySubgroup ℂ,
                  ((Matrix.GeneralLinearGroup.map
                    (@AlgEquiv.toRingEquiv ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _
                      (Algebra.TensorProduct.rid ℝ ℝ ℂ)).toRingHom
                    g : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
                    !![(b₁ : ℂ), (b₁ : ℂ) * v; 0, (b₂ : ℂ)] *
                      ((k : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)}).toReal /
              (τ {t |
                  (((Matrix.GeneralLinearGroup.map
                    (@AlgEquiv.toRingEquiv ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _
                      (Algebra.TensorProduct.rid ℝ ℝ ℂ)).toRingHom
                    (t : GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) 0 0).re ∈
                    Set.Icc (1 : ℝ) (Real.exp 1) ∧
                  (((Matrix.GeneralLinearGroup.map
                    (@AlgEquiv.toRingEquiv ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _
                      (Algebra.TensorProduct.rid ℝ ℝ ℂ)).toRingHom
                    (t : GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) 1 1).re ∈
                    Set.Icc (1 : ℝ) (Real.exp 1)}).toReal : ℝ) : ℂ) *
                twistedSplitTransform φ a₁ a₂ / ((4 * |a₁ - a₂| : ℝ) : ℂ))) ∧
    (∀ (r θ : ℝ), 0 < r → Real.sin θ ≠ 0 →
      ∀ δ : GL (Fin 2) (ℂ ⊗[ℝ] ℝ),
        ((Matrix.GeneralLinearGroup.map
          (@AlgEquiv.toRingEquiv ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _
            (Algebra.TensorProduct.rid ℝ ℝ ℂ)).toRingHom
          δ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
          !![((Real.sqrt r * Real.cos (θ / 2) : ℝ) : ℂ), ((Real.sqrt r * Real.sin (θ / 2) : ℝ) : ℂ);
            ((-(Real.sqrt r * Real.sin (θ / 2)) : ℝ) : ℂ), ((Real.sqrt r * Real.cos (θ / 2) : ℝ) : ℂ)] →
        ∀ (τ : @Measure (twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ)
            (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ)),
          @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ) τ →
          ∀ I : ℂ,
            IsTwistedOrbitalIntegralOn ℝ ℂ ℝ Complex.conjAe μ δ τ
              (fun y => φ
                (Matrix.GeneralLinearGroup.map
                  (@AlgEquiv.toRingEquiv ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _
                    (Algebra.TensorProduct.rid ℝ ℝ ℂ)).toRingHom y : GL (Fin 2) ℂ)) I →
            I = (((
              (μ {g | ∃ b₁ ∈ Set.Icc (1 : ℝ) (Real.exp 1), ∃ b₂ ∈ Set.Icc (1 : ℝ) (Real.exp 1),
                  ∃ v : ℂ, v.re ∈ Set.Icc (0 : ℝ) 1 ∧ v.im ∈ Set.Icc (0 : ℝ) 1 ∧
                  ∃ k : AutomorphicForm.WindowedSiegel.rowIsometrySubgroup ℂ,
                  ((Matrix.GeneralLinearGroup.map
                    (@AlgEquiv.toRingEquiv ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _
                      (Algebra.TensorProduct.rid ℝ ℝ ℂ)).toRingHom
                    g : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
                    !![(b₁ : ℂ), (b₁ : ℂ) * v; 0, (b₂ : ℂ)] *
                      ((k : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)}).toReal /
              (τ {t | (Matrix.det
                  ((Matrix.GeneralLinearGroup.map
                    (@AlgEquiv.toRingEquiv ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _
                      (Algebra.TensorProduct.rid ℝ ℝ ℂ)).toRingHom
                    (t : GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)).re ∈
                    Set.Icc (1 : ℝ) (Real.exp 2)}).toReal : ℝ) : ℂ) *
                twistedEllipticTransform φ r θ / (8 * Real.sin θ ^ 2 : ℂ))) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_GL2Twisted_twistedOrbitalIntegral_eq_twistedSplitTransform_div_and_eq_twistedEllipticTransform_div.solution
