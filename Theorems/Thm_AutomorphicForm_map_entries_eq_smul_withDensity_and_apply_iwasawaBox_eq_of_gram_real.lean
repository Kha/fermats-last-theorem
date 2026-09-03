import Definitions.Def_AutomorphicForm_TwistedOrbital
import P2M.Util
import P2M.Sol.S_AutomorphicForm_map_entries_eq_smul_withDensity_and_apply_iwasawaBox_eq_of_gram_real

set_option autoImplicit false

open MeasureTheory AutomorphicForm
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.map_entries_eq_smul_withDensity_and_apply_iwasawaBox_eq_of_gram_real
    (c : ℝˣ)
    (τ : @Measure (Subgroup.centralizer
        ({Matrix.GeneralLinearGroup.scalar (Fin 2) c} : Set (GL (Fin 2) ℝ)))
        (centralizerBorel ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) c)))
    (n₁ : ℕ) (e₁ : Fin n₁ → Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ)) (s : ENNReal)
    (hli : LinearIndependent ℝ e₁)
    (hspan : (Submodule.span ℝ (Set.range e₁) : Set (Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ))) =
      Set.range (fun Y : Matrix (Fin 2) (Fin 2) ℝ =>
        Y.map (fun x : ℝ => ((1 : ℂ) ⊗ₜ[ℝ] x : ℂ ⊗[ℝ] ℝ))))
    (hτ : (letI : MeasurableSpace (Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ)) := borel _
       letI := centralizerBorel ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) c)
       Measure.map (fun t : ↥(Subgroup.centralizer
             ({Matrix.GeneralLinearGroup.scalar (Fin 2) c} : Set (GL (Fin 2) ℝ))) =>
           ((t : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).map
             (fun x : ℝ => ((1 : ℂ) ⊗ₜ[ℝ] x : ℂ ⊗[ℝ] ℝ))) τ =
         s • ((ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j : Fin n₁ =>
                 Algebra.trace ℝ (ℂ ⊗[ℝ] ℝ) (Matrix.trace (e₁ i * e₁ j))).det|)) •
               Measure.map (fun a : Fin n₁ → ℝ => ∑ i, a i • e₁ i) volume).withDensity
             (fun X : Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ) =>
               (ENNReal.ofReal |Algebra.norm ℝ (Matrix.det X)|)⁻¹))) :
    (letI := centralizerBorel ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) c)
     Measure.map (fun t : ↥(Subgroup.centralizer
           ({Matrix.GeneralLinearGroup.scalar (Fin 2) c} : Set (GL (Fin 2) ℝ))) =>
         fun i j : Fin 2 => ((t : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) i j) τ =
       (4 * s) • (volume : Measure (Fin 2 → Fin 2 → ℝ)).withDensity
         (fun q => (ENNReal.ofReal ((Matrix.of q).det ^ 2))⁻¹)) ∧
    τ {t | ∃ b₁ ∈ Set.Icc (1 : ℝ) (Real.exp 1), ∃ b₂ ∈ Set.Icc (1 : ℝ) (Real.exp 1),
        ∃ x ∈ Set.Icc (0 : ℝ) 1, ∃ k : rowIsometrySubgroup₀ ℝ,
        ((t : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
          !![b₁, b₁ * x; 0, b₂] * ((k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)} =
      s * ENNReal.ofReal (8 * Real.pi) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_map_entries_eq_smul_withDensity_and_apply_iwasawaBox_eq_of_gram_real.solution
