import Definitions.Def_AutomorphicForm_TwistedOrbital
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_contDiff_hasCompactSupport_forall_isTwistedOrbitalIntegralOn_conjAe_imp_eq

set_option autoImplicit false

open MeasureTheory AutomorphicForm
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.exists_contDiff_hasCompactSupport_forall_isTwistedOrbitalIntegralOn_conjAe_imp_eq
    (P : Type) [NormedAddCommGroup P] [NormedSpace ℝ P]
    (μA : @Measure (GL (Fin 2) ℝ) (glBorelOf ℝ))
    (μL : @Measure (GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) (glBorelOf (ℂ ⊗[ℝ] ℝ)))
    (Φ : (Fin 2 → Fin 2 → ℂ) × P → ℂ)
    (hΦs : ContDiff ℝ (⊤ : ℕ∞) Φ) (hΦc : HasCompactSupport Φ)
    (hΦU : tsupport Φ ⊆ {q | IsUnit (Matrix.det (Matrix.of q.1))})
    (hΦr : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : rowIsometrySubgroup₀ ℂ =>
      fun q : (Fin 2 → Fin 2 → ℂ) × P =>
        Φ (Matrix.of.symm (Matrix.of q.1 * ((k : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)), q.2))))
    (hΦl : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : rowIsometrySubgroup₀ ℂ =>
      fun q : (Fin 2 → Fin 2 → ℂ) × P =>
        Φ (Matrix.of.symm (((k : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) * Matrix.of q.1), q.2))))
    (hμA : @Measure.IsHaarMeasure _ _ _ (glBorelOf ℝ) μA)
    (hμL : @Measure.IsHaarMeasure _ _ _ (glBorelOf (ℂ ⊗[ℝ] ℝ)) μL) :
    ∃ F : (Fin 2 → Fin 2 → ℝ) × P → ℂ,
      ContDiff ℝ (⊤ : ℕ∞) F ∧ HasCompactSupport F ∧ tsupport F ⊆ {r | IsUnit (Matrix.det (Matrix.of r.1))} ∧
      FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : rowIsometrySubgroup₀ ℝ =>
        fun r : (Fin 2 → Fin 2 → ℝ) × P =>
          F (Matrix.of.symm (Matrix.of r.1 * ((k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)), r.2))) ∧
      FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : rowIsometrySubgroup₀ ℝ =>
        fun r : (Fin 2 → Fin 2 → ℝ) × P =>
          F (Matrix.of.symm (((k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) * Matrix.of r.1), r.2))) ∧
      (∀ (n : ℕ) (c : Fin n → ℂ) (q : Fin n → P),
        (∀ E : Fin 2 → Fin 2 → ℂ, ∑ j, c j * Φ (E, q j) = 0) →
          ∀ E' : Fin 2 → Fin 2 → ℝ, ∑ j, c j * F (E', q j) = 0) ∧
      (∀ p : P, ∀ γ : GL (Fin 2) ℝ, IsRegularSemisimple γ →
        ∀ δ : GL (Fin 2) (ℂ ⊗[ℝ] ℝ), IsNormConjugator ℝ ℂ ℝ Complex.conjAe γ δ 1 →
        ∀ (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) ℝ))) (centralizerBorel ℝ γ))
          (τ' : @Measure (twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ)
            (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ)),
          @Measure.IsHaarMeasure _ _ _ (centralizerBorel ℝ γ) τ →
          @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ) τ' →
          Coupled ℝ ℂ ℝ Complex.conjAe γ δ 1 τ τ' →
          ∀ I I' : ℂ,
            IsTwistedOrbitalIntegralOn ℝ ℂ ℝ Complex.conjAe μL δ τ'
              (fun y => Φ (Matrix.of.symm
                ((Matrix.GeneralLinearGroup.map
                  (@AlgEquiv.toRingEquiv ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _
                    (Algebra.TensorProduct.rid ℝ ℝ ℂ)).toRingHom y : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ),
                p)) I' →
            IsOrbitalIntegralOn ℝ μA γ τ (fun g => F (Matrix.of.symm (g : Matrix (Fin 2) (Fin 2) ℝ), p)) I →
            I' = I) ∧
      (∀ p : P, ∀ γ : GL (Fin 2) ℝ, IsRegularSemisimple γ → (¬ ∃ δ, IsNormOf ℝ ℂ ℝ Complex.conjAe γ δ) →
        ∀ τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) ℝ))) (centralizerBorel ℝ γ),
          @Measure.IsHaarMeasure _ _ _ (centralizerBorel ℝ γ) τ →
          ∀ I : ℂ, IsOrbitalIntegralOn ℝ μA γ τ (fun g => F (Matrix.of.symm (g : Matrix (Fin 2) (Fin 2) ℝ), p)) I →
            I = 0) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_contDiff_hasCompactSupport_forall_isTwistedOrbitalIntegralOn_conjAe_imp_eq.solution
