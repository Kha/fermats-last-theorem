import Definitions.Def_AutomorphicForm_TwistedOrbital
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_elliptic_family_coupled_inf_twistedCentralizer_conjAe_of_neg
attribute [-simp] LT.TwistedNorm.sigmaPartialNorm_zero LT.TwistedNorm.GL2.traceDetCompanion_apply_10 LT.TwistedNorm.GL2.traceDetCompanion_apply_00 LT.TwistedNorm.GL2.traceDetCompanion_apply_01 LT.TwistedNorm.GL2.traceDetCompanion_apply_11

set_option autoImplicit false

open MeasureTheory AutomorphicForm
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.exists_elliptic_family_coupled_inf_twistedCentralizer_conjAe_of_neg
    (c : ℝˣ) (hc : (c : ℝ) < 0)
    (δ y : GL (Fin 2) (ℂ ⊗[ℝ] ℝ))
    (hδ : IsNormConjugator ℝ ℂ ℝ Complex.conjAe (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ y) :
    ∃ (γ : ℝ → GL (Fin 2) ℝ) (θ₀ θ₁ : ℝ) (u : ℝ → GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) (y₁ : GL (Fin 2) (ℂ ⊗[ℝ] ℝ))
      (νT : @Measure (GL (Fin 2) ℝ) (glBorelOf ℝ))
      (τ : ∀ θ : ℝ, @Measure (Subgroup.centralizer ({γ θ} : Set (GL (Fin 2) ℝ))) (centralizerBorel ℝ (γ θ)))
      (τS : @Measure ↥(twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ ⊓ twistedCentralizer ℝ ℂ ℝ Complex.conjAe (u θ₁ * δ))
        (borel _))
      (τu : ∀ θ : ℝ, @Measure (twistedCentralizer ℝ ℂ ℝ Complex.conjAe (u θ * δ))
        (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe (u θ * δ))),
      (∀ θ : ℝ, ((γ θ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
        (c : ℝ) • !![Real.cos θ, -Real.sin θ; Real.sin θ, Real.cos θ]) ∧
      0 < θ₀ ∧ θ₁ ∈ Set.Ioo 0 θ₀ ∧
      (∀ θ : ℝ, u θ ∈ twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ ⊓ twistedCentralizer ℝ ℂ ℝ Complex.conjAe (u θ₁ * δ)) ∧
      (letI := glBorelOf (ℂ ⊗[ℝ] ℝ)
       Filter.Tendsto u (nhdsWithin 0 (Set.Ioi 0)) (nhds 1)) ∧
      (letI := glBorelOf ℝ
       Filter.Tendsto γ (nhdsWithin 0 (Set.Ioi 0)) (nhds (Matrix.GeneralLinearGroup.scalar (Fin 2) c))) ∧
      @Measure.IsHaarMeasure _ _ _ (borel _) τS ∧
      ∀ θ ∈ Set.Ioo 0 θ₀,
        IsRegularSemisimple (γ θ) ∧
        IsRegularSemisimple (normString ℝ ℂ ℝ Complex.conjAe (u θ * δ)) ∧
        IsNormConjugator ℝ ℂ ℝ Complex.conjAe (γ θ) (u θ * δ) y₁ ∧
        @Measure.IsHaarMeasure _ _ _ (centralizerBorel ℝ (γ θ)) (τ θ) ∧
        @Measure.map _ _ (centralizerBorel ℝ (γ θ)) (glBorelOf ℝ) Subtype.val (τ θ) = νT ∧
        @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe (u θ * δ)) (τu θ) ∧
        (letI := glBorelOf (ℂ ⊗[ℝ] ℝ)
         letI := twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe (u θ * δ)
         letI : MeasurableSpace ↥(twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ ⊓
             twistedCentralizer ℝ ℂ ℝ Complex.conjAe (u θ₁ * δ)) := borel _
         Measure.map Subtype.val (τu θ) = Measure.map Subtype.val τS) ∧
        Coupled ℝ ℂ ℝ Complex.conjAe (γ θ) (u θ * δ) y₁ (τ θ) (τu θ) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_elliptic_family_coupled_inf_twistedCentralizer_conjAe_of_neg.solution
