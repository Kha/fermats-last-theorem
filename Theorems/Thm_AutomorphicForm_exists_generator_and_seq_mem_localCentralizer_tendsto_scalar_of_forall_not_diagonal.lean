import Definitions.Def_AutomorphicForm_TwistedOrbital
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_generator_and_seq_mem_localCentralizer_tendsto_scalar_of_forall_not_diagonal

set_option autoImplicit false

open MeasureTheory NumberField
open IsDedekindDomain
open scoped TensorProduct
open scoped TensorProduct.RightActions

theorem AutomorphicForm.exists_generator_and_seq_mem_localCentralizer_tendsto_scalar_of_forall_not_diagonal
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (c : (v.adicCompletion K)ˣ) (ϖ : v.adicCompletion K)
    (hϖ : Valued.v ϖ = Multiplicative.ofAdd (-1 : ℤ))
    (γ₀ : GL (Fin 2) (v.adicCompletion K)) (_hreg : AutomorphicForm.IsRegularSemisimple γ₀)
    (_hns : ∀ g : GL (Fin 2) (v.adicCompletion K),
      ¬ (((g⁻¹ * γ₀ * g : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 1 = 0 ∧
         ((g⁻¹ * γ₀ * g : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 0 = 0)) :
    ∃ (Y : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) (γ : ℕ → GL (Fin 2) (v.adicCompletion K)),
      (Valued.v Y.det ≤ 1 ∧ Valued.v Y.trace ≤ 1) ∧
      (∀ b : v.adicCompletion K, Valued.v b ≤ 1 →
        ¬ (Valued.v (Y - b • 1).det ≤ Valued.v ϖ ^ 2 ∧ Valued.v (Y - b • 1).trace ≤ Valued.v ϖ)) ∧
      (∀ m : ℕ, 1 ≤ m →
        γ m ∈ AutomorphicForm.localCentralizer K v γ₀ ∧
        AutomorphicForm.IsRegularSemisimple (γ m) ∧
        Valued.v ((((c⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) •
          ((γ m : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))).det) = 1 ∧
        ((c⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) •
            ((γ m : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))
          = (1 : v.adicCompletion K) • 1 + (ϖ ^ m) • Y ∧
        AutomorphicForm.localCentralizer K v (γ m) = AutomorphicForm.localCentralizer K v γ₀) ∧
      Filter.Tendsto γ Filter.atTop (nhds (Matrix.GeneralLinearGroup.scalar (Fin 2) c)) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_generator_and_seq_mem_localCentralizer_tendsto_scalar_of_forall_not_diagonal.solution
