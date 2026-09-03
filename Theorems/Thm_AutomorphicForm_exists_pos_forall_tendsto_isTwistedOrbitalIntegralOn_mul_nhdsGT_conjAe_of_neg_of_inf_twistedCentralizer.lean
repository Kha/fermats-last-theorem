import Definitions.Def_AutomorphicForm_TwistedOrbital
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_pos_forall_tendsto_isTwistedOrbitalIntegralOn_mul_nhdsGT_conjAe_of_neg_of_inf_twistedCentralizer

set_option autoImplicit false

p2m_open "MeasureTheory AutomorphicForm~exists_isCompact_forall_twistedCentralizer_conjAe_eq_scalar_mul_of_neg~exists_nhds_isCompact_forall_twistedCentralizer_conjAe_mul_mem_of_neg"
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.exists_pos_forall_tendsto_isTwistedOrbitalIntegralOn_mul_nhdsGT_conjAe_of_neg_of_inf_twistedCentralizer
    (μL : @Measure (GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) (glBorelOf (ℂ ⊗[ℝ] ℝ)))
    (hμL : @Measure.IsHaarMeasure _ _ _ (glBorelOf (ℂ ⊗[ℝ] ℝ)) μL)
    (c : ℝˣ) (hc : (c : ℝ) < 0)
    (δ y : GL (Fin 2) (ℂ ⊗[ℝ] ℝ))
    (hδ : IsNormConjugator ℝ ℂ ℝ Complex.conjAe (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ y)
    (τ' : @Measure (twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ)
      (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ))
    (hτ' : @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ) τ')
    (u₀ : GL (Fin 2) (ℂ ⊗[ℝ] ℝ))
    (τS : @Measure ↥(twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ ⊓ twistedCentralizer ℝ ℂ ℝ Complex.conjAe (u₀ * δ)) (borel _))
    (hτS : @Measure.IsHaarMeasure _ _ _ (borel _) τS) :
    ∃ κ : ℝ, 0 < κ ∧
      (∀ w : ↥(twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ) → ℝ,
        (letI := twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ
         letI : MeasurableSpace ↥(twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ ⊓
             twistedCentralizer ℝ ℂ ℝ Complex.conjAe (u₀ * δ)) := borel _
         (∀ t, 0 ≤ w t) ∧ Measurable w ∧ HasCompactSupport w ∧
           ∀ t : ↥(twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ),
             ∫ s : ↥(twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ ⊓ twistedCentralizer ℝ ℂ ℝ Complex.conjAe (u₀ * δ)),
               w ((⟨(s : GL (Fin 2) (ℂ ⊗[ℝ] ℝ)), (Subgroup.mem_inf.mp s.2).1⟩ :
                 ↥(twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ)) * t) ∂τS = 1) →
        (letI := twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ
         ∫ t, w t ∂τ' = κ)) ∧
      ∀ (φ : GL (Fin 2) ℂ → ℂ),
        ((∃ Φ : (Fin 2 → Fin 2 → ℂ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) Φ ∧
          ∀ g, φ g = Φ (fun i j => (g : Matrix (Fin 2) (Fin 2) ℂ) i j)) ∧ HasCompactSupport φ) →
      ∀ (θ₀ : ℝ), 0 < θ₀ →
      ∀ (u : ℝ → GL (Fin 2) (ℂ ⊗[ℝ] ℝ)),
        (∀ θ : ℝ, u θ ∈ twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ ⊓ twistedCentralizer ℝ ℂ ℝ Complex.conjAe (u₀ * δ)) →
        (letI := glBorelOf (ℂ ⊗[ℝ] ℝ)
         Filter.Tendsto u (nhdsWithin 0 (Set.Ioi 0)) (nhds 1)) →
        (∀ θ ∈ Set.Ioo 0 θ₀, IsRegularSemisimple (normString ℝ ℂ ℝ Complex.conjAe (u θ * δ))) →
      ∀ (τu : ∀ θ : ℝ, @Measure (twistedCentralizer ℝ ℂ ℝ Complex.conjAe (u θ * δ))
          (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe (u θ * δ))),
        (∀ θ ∈ Set.Ioo 0 θ₀, @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe (u θ * δ)) (τu θ)) →
        (∀ θ ∈ Set.Ioo 0 θ₀,
          (letI := glBorelOf (ℂ ⊗[ℝ] ℝ)
           letI := twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe (u θ * δ)
           letI : MeasurableSpace ↥(twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ ⊓
               twistedCentralizer ℝ ℂ ℝ Complex.conjAe (u₀ * δ)) := borel _
           Measure.map Subtype.val (τu θ) = Measure.map Subtype.val τS)) →
      ∀ (Ψ : ℝ → ℂ),
        (∀ θ ∈ Set.Ioo 0 θ₀,
          IsTwistedOrbitalIntegralOn ℝ ℂ ℝ Complex.conjAe μL (u θ * δ) (τu θ)
            (fun z => φ (Matrix.GeneralLinearGroup.map
                (@AlgEquiv.toRingEquiv ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _
                  (Algebra.TensorProduct.rid ℝ ℝ ℂ)).toRingHom z : GL (Fin 2) ℂ)) (Ψ θ)) →
      ∀ I' : ℂ,
        IsTwistedOrbitalIntegralOn ℝ ℂ ℝ Complex.conjAe μL δ τ'
            (fun z => φ (Matrix.GeneralLinearGroup.map
                (@AlgEquiv.toRingEquiv ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _
                  (Algebra.TensorProduct.rid ℝ ℝ ℂ)).toRingHom z : GL (Fin 2) ℂ)) I' →
        Filter.Tendsto Ψ (nhdsWithin 0 (Set.Ioi 0)) (nhds ((κ : ℂ) * I')) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_pos_forall_tendsto_isTwistedOrbitalIntegralOn_mul_nhdsGT_conjAe_of_neg_of_inf_twistedCentralizer.solution
