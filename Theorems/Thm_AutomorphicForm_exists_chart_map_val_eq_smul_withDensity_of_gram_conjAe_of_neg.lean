import Definitions.Def_AutomorphicForm_TwistedOrbital
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_chart_map_val_eq_smul_withDensity_of_gram_conjAe_of_neg

set_option autoImplicit false

open MeasureTheory AutomorphicForm
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.exists_chart_map_val_eq_smul_withDensity_of_gram_conjAe_of_neg
    (c : ℝˣ) (hc : (c : ℝ) < 0)
    (δ y : GL (Fin 2) (ℂ ⊗[ℝ] ℝ))
    (hδ : IsNormConjugator ℝ ℂ ℝ Complex.conjAe (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ y)
    (τ' : @Measure (twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ)
      (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ))
    (n₂ : ℕ) (e₂ : Fin n₂ → Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ)) (s : ENNReal)
    (hgram₂ : (letI : MeasurableSpace (Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ)) := borel _
       letI := twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ
       LinearIndependent ℝ e₂ ∧
           (Submodule.span ℝ (Set.range e₂) : Set (Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ))) =
             {X | X * (δ : Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ)) =
               (δ : Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ)) * X.map (sigmaTensor ℝ ℂ ℝ Complex.conjAe)} ∧
         Measure.map (fun t : ↥(twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ) =>
             ((t : GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) : Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ))) τ' =
           s • ((ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j : Fin n₂ =>
                   Algebra.trace ℝ (ℂ ⊗[ℝ] ℝ) (Matrix.trace (e₂ i * e₂ j))).det|)) •
                 Measure.map (fun a : Fin n₂ → ℝ => ∑ i, a i • e₂ i) volume).withDensity
               (fun X : Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ) =>
                 (ENNReal.ofReal |Algebra.norm ℝ (Matrix.det X)|)⁻¹))) :
    letI : MeasurableSpace (Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ)) := borel _
    letI := twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ
    ∃ φ : (Fin 4 → ℝ) →ₗ[ℝ] Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ),
      Function.Injective φ ∧
      (∀ a : Fin 4 → ℝ, Matrix.det (φ a) = ((1 : ℂ) ⊗ₜ[ℝ] (a 0 ^ 2 + a 1 ^ 2 - (c : ℝ) * (a 2 ^ 2 + a 3 ^ 2)) : ℂ ⊗[ℝ] ℝ)) ∧
      Measure.map (fun t : ↥(twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ) =>
          ((t : GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) : Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ))) τ' =
        (ENNReal.ofReal (16 * |(c : ℝ)|) * s) •
          (Measure.map φ (volume : Measure (Fin 4 → ℝ))).withDensity
            (fun X : Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ) => (ENNReal.ofReal |Algebra.norm ℝ (Matrix.det X)|)⁻¹) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_chart_map_val_eq_smul_withDensity_of_gram_conjAe_of_neg.solution
