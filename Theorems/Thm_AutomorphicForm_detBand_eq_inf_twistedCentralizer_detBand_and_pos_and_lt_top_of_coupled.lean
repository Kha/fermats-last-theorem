import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_GL2RealOrbitalTransforms
import P2M.Util
import P2M.Sol.S_AutomorphicForm_detBand_eq_inf_twistedCentralizer_detBand_and_pos_and_lt_top_of_coupled

set_option autoImplicit false

open MeasureTheory AutomorphicForm AutomorphicForm.GL2Real
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.detBand_eq_inf_twistedCentralizer_detBand_and_pos_and_lt_top_of_coupled
    (c : ℝˣ) (δ : GL (Fin 2) (ℂ ⊗[ℝ] ℝ))
    (u₀ : GL (Fin 2) (ℂ ⊗[ℝ] ℝ))
    (τS : @Measure ↥(twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ ⊓ twistedCentralizer ℝ ℂ ℝ Complex.conjAe (u₀ * δ)) (borel _))
    (hτS : @Measure.IsHaarMeasure _ _ _ (borel _) τS)
    (θ₁ : ℝ) (γ₀ : GL (Fin 2) ℝ)
    (hγ₀ : ((γ₀ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      (c : ℝ) • !![Real.cos θ₁, -Real.sin θ₁; Real.sin θ₁, Real.cos θ₁])
    (hreg : IsRegularSemisimple γ₀)
    (y₀ : GL (Fin 2) (ℂ ⊗[ℝ] ℝ))
    (hn₀ : IsNormConjugator ℝ ℂ ℝ Complex.conjAe γ₀ (u₀ * δ) y₀)
    (τT : @Measure (Subgroup.centralizer ({γ₀} : Set (GL (Fin 2) ℝ))) (centralizerBorel ℝ γ₀))
    (hτT : @Measure.IsHaarMeasure _ _ _ (centralizerBorel ℝ γ₀) τT)
    (νT : @Measure (GL (Fin 2) ℝ) (glBorelOf ℝ))
    (hνT : @Measure.map _ _ (centralizerBorel ℝ γ₀) (glBorelOf ℝ) Subtype.val τT = νT)
    (τu : @Measure (twistedCentralizer ℝ ℂ ℝ Complex.conjAe (u₀ * δ))
      (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe (u₀ * δ)))
    (hτu : @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe (u₀ * δ)) τu)
    (hτuS : (letI := glBorelOf (ℂ ⊗[ℝ] ℝ)
       letI := twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe (u₀ * δ)
       letI : MeasurableSpace ↥(twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ ⊓
           twistedCentralizer ℝ ℂ ℝ Complex.conjAe (u₀ * δ)) := borel _
       Measure.map Subtype.val τu = Measure.map Subtype.val τS))
    (hcoup : Coupled ℝ ℂ ℝ Complex.conjAe γ₀ (u₀ * δ) y₀ τT τu) :
    νT {g : GL (Fin 2) ℝ | Matrix.det (g : Matrix (Fin 2) (Fin 2) ℝ) ∈ Set.Icc (1 : ℝ) (Real.exp 2)} =
        τS {t : ↥(twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ ⊓ twistedCentralizer ℝ ℂ ℝ Complex.conjAe (u₀ * δ)) |
        ∃ d ∈ Set.Icc (1 : ℝ) (Real.exp 2),
        Matrix.det ((t : GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) : Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ)) = ((1 : ℂ) ⊗ₜ[ℝ] d : ℂ ⊗[ℝ] ℝ)} ∧
      0 < νT {g : GL (Fin 2) ℝ | Matrix.det (g : Matrix (Fin 2) (Fin 2) ℝ) ∈ Set.Icc (1 : ℝ) (Real.exp 2)} ∧ νT {g : GL (Fin 2) ℝ | Matrix.det (g : Matrix (Fin 2) (Fin 2) ℝ) ∈ Set.Icc (1 : ℝ) (Real.exp 2)} < ⊤ := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_detBand_eq_inf_twistedCentralizer_detBand_and_pos_and_lt_top_of_coupled.solution
