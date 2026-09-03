import Definitions.Def_AutomorphicForm_TwistedOrbital
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_pos_forall_integral_eq_and_forall_nhds_isTwistedOrbitalIntegral_mul_eq_mul_of_not_isSigmaConjugate_scalar_of_finrank_eq_two

set_option autoImplicit false

open MeasureTheory NumberField
open IsDedekindDomain
open scoped TensorProduct
open scoped TensorProduct.RightActions

theorem AutomorphicForm.exists_pos_forall_integral_eq_and_forall_nhds_isTwistedOrbitalIntegral_mul_eq_mul_of_not_isSigmaConjugate_scalar_of_finrank_eq_two
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (v : HeightOneSpectrum (𝓞 K))
    (c : (v.adicCompletion K)ˣ)
    (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hδ : AutomorphicForm.IsNormOf K L (v.adicCompletion K) σ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ)
    (hδq : ∀ z : (L ⊗[K] v.adicCompletion K)ˣ,
      ¬ AutomorphicForm.IsSigmaConjugate K L (v.adicCompletion K) σ δ (Matrix.GeneralLinearGroup.scalar (Fin 2) z))
    (τ' : @Measure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ)
      (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ δ))
    (hτ' : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ δ) τ')
    (u₀ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (τS : @Measure ↥(AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ ⊓
        AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ (u₀ * δ)) (borel _))
    (hτS : @Measure.IsHaarMeasure _ _ _ (borel _) τS) :
    ∃ ρ : ℝ, 0 < ρ ∧
      (∀ w : ↥(AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ) → ℝ,
        (letI := AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ δ
         letI : MeasurableSpace ↥(AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ ⊓
             AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ (u₀ * δ)) := borel _
         (∀ t, 0 ≤ w t) ∧ Measurable w ∧ HasCompactSupport w ∧
           ∀ t : ↥(AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ),
             ∫ s : ↥(AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ ⊓
                 AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ (u₀ * δ)),
               w ((⟨(s : GL (Fin 2) (L ⊗[K] v.adicCompletion K)), (Subgroup.mem_inf.mp s.2).1⟩ :
                 ↥(AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ)) * t) ∂τS = 1) →
        (letI := AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ δ
         ∫ t, w t ∂τ' = ρ)) ∧
      ∀ (φv : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ), AutomorphicForm.IsSemiLocalTestFn K L v φv →
        ∃ V ∈ nhds (1 : GL (Fin 2) (L ⊗[K] v.adicCompletion K)), ∀ u ∈ V,
          u ∈ AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ ⊓
              AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ (u₀ * δ) →
          AutomorphicForm.IsRegularSemisimple (AutomorphicForm.normString K L (v.adicCompletion K) σ (u * δ)) →
          ∀ (τu : @Measure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ (u * δ))
              (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ (u * δ))),
            @Measure.IsHaarMeasure _ _ _
              (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ (u * δ)) τu →
            (letI := AutomorphicForm.glBorelOf (L ⊗[K] v.adicCompletion K);
              letI := AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ (u * δ);
              letI : MeasurableSpace ↥(AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ ⊓
                  AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ (u₀ * δ)) := borel _;
              Measure.map Subtype.val τu = Measure.map Subtype.val τS) →
            ∀ J I : ℂ, AutomorphicForm.IsTwistedOrbitalIntegral K L v σ (u * δ) τu φv J →
              AutomorphicForm.IsTwistedOrbitalIntegral K L v σ δ τ' φv I → J = (ρ : ℂ) * I := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_pos_forall_integral_eq_and_forall_nhds_isTwistedOrbitalIntegral_mul_eq_mul_of_not_isSigmaConjugate_scalar_of_finrank_eq_two.solution
