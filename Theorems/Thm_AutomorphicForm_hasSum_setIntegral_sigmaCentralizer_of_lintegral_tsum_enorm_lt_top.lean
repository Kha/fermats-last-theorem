import Definitions.Def_TwistedNormClasses
import Definitions.Def_AutomorphicForm_SigmaCentralizer
import Definitions.Def_AutomorphicForm_AdelicLsXi
import P2M.Util
import P2M.Sol.S_AutomorphicForm_hasSum_setIntegral_sigmaCentralizer_of_lintegral_tsum_enorm_lt_top

set_option autoImplicit false

theorem AutomorphicForm.hasSum_setIntegral_sigmaCentralizer_of_lintegral_tsum_enorm_lt_top
    (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
    (R : Type) [CommRing R] [IsDedekindDomain R] [Algebra R L] [IsFractionRing R L]
    [MeasurableSpace (AutomorphicForm.AdelicGL2 R L)] [BorelSpace (AutomorphicForm.AdelicGL2 R L)]
    (σ : L ≃ₐ[K] L)
    (σA : AutomorphicForm.AdelicGL2 R L →* AutomorphicForm.AdelicGL2 R L) (hσAc : Continuous σA)
    (hσA : ∀ γ : GL (Fin 2) L,
      σA (AutomorphicForm.globalPoints R L γ) =
        AutomorphicForm.globalPoints R L (Matrix.GeneralLinearGroup.map (σ : L →+* L) γ))
    (μ : MeasureTheory.Measure (AutomorphicForm.AdelicGL2 R L))
    [MeasureTheory.SMulInvariantMeasure (AutomorphicForm.globalPoints R L).range
      (AutomorphicForm.AdelicGL2 R L) μ]
    (Φ : Set (AutomorphicForm.AdelicGL2 R L))
    (hΦ : MeasureTheory.IsFundamentalDomain (AutomorphicForm.globalPoints R L).range Φ μ)
    (C : Set (LT.TwistedNorm.SigmaConjClasses σ))
    (rep : LT.TwistedNorm.SigmaConjClasses σ → GL (Fin 2) L)
    (hrep : ∀ c ∈ C, LT.TwistedNorm.SigmaConjClasses.mk σ (rep c) = c)
    (Ψ : LT.TwistedNorm.SigmaConjClasses σ → Set (AutomorphicForm.AdelicGL2 R L))
    (hΨ : ∀ c ∈ C, MeasureTheory.IsFundamentalDomain
      ((AutomorphicForm.sigmaCentralizer (Matrix.GeneralLinearGroup.map (σ : L →+* L)) (rep c)).map
        (AutomorphicForm.globalPoints R L)) (Ψ c) μ)
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : AutomorphicForm.AdelicGL2 R L → E) (hF : MeasureTheory.StronglyMeasurable F)
    (habs : ∫⁻ x in Φ, ∑' δ : {δ : GL (Fin 2) L // LT.TwistedNorm.SigmaConjClasses.mk σ δ ∈ C},
        ‖F (x⁻¹ * AutomorphicForm.globalPoints R L δ * σA x)‖ₑ ∂μ < ⊤) :
    (∑' c : C, ∫⁻ x in Ψ c, ‖F (x⁻¹ * AutomorphicForm.globalPoints R L (rep c) * σA x)‖ₑ ∂μ =
        ∫⁻ x in Φ, ∑' δ : {δ : GL (Fin 2) L // LT.TwistedNorm.SigmaConjClasses.mk σ δ ∈ C},
          ‖F (x⁻¹ * AutomorphicForm.globalPoints R L δ * σA x)‖ₑ ∂μ) ∧
    (∀ c ∈ C, MeasureTheory.IntegrableOn
        (fun x => F (x⁻¹ * AutomorphicForm.globalPoints R L (rep c) * σA x)) (Ψ c) μ) ∧
      HasSum (fun c : C => ∫ x in Ψ c, F (x⁻¹ * AutomorphicForm.globalPoints R L (rep c) * σA x) ∂μ)
        (∫ x in Φ, ∑' δ : {δ : GL (Fin 2) L // LT.TwistedNorm.SigmaConjClasses.mk σ δ ∈ C},
          F (x⁻¹ * AutomorphicForm.globalPoints R L δ * σA x) ∂μ) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_hasSum_setIntegral_sigmaCentralizer_of_lintegral_tsum_enorm_lt_top.solution
