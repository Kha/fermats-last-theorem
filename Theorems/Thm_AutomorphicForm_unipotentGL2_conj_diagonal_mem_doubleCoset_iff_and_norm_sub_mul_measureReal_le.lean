import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AutomorphicForm_ConstantTerm
import P2M.Util
import P2M.Sol.S_AutomorphicForm_unipotentGL2_conj_diagonal_mem_doubleCoset_iff_and_norm_sub_mul_measureReal_le

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open scoped Pointwise

theorem AutomorphicForm.unipotentGL2_conj_diagonal_mem_doubleCoset_iff_and_norm_sub_mul_measureReal_le
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (ϖ : v.adicCompletionIntegers K) (hϖ : Irreducible ϖ) (m₁ m₂ : ℤ) (hm : m₂ ≤ m₁)
    (dl : GL (Fin 2) (v.adicCompletion K))
    (hdl : (dl : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      Matrix.diagonal ![(ϖ : v.adicCompletion K) ^ m₁, (ϖ : v.adicCompletion K) ^ m₂])
    (a b : v.adicCompletion K) (hab : a ≠ b) (t : GL (Fin 2) (v.adicCompletion K))
    (ht : (t : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) = Matrix.diagonal ![a, b])
    [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]
    (ν : Measure (v.adicCompletion K)) [ν.IsAddHaarMeasure] :
    ‖(ϖ : v.adicCompletion K)‖ = ((Ideal.absNorm v.asIdeal : ℝ))⁻¹ ∧
    (∀ u : v.adicCompletion K,
      (AutomorphicForm.unipotentGL2 u)⁻¹ * t * AutomorphicForm.unipotentGL2 u ∈
          AutomorphicForm.localIntegralSet K v * ({dl} : Set (GL (Fin 2) (v.adicCompletion K))) *
            AutomorphicForm.localIntegralSet K v ↔
        ‖a * b‖ = ‖(ϖ : v.adicCompletion K)‖ ^ (m₁ + m₂) ∧
          max (max ‖a‖ ‖b‖) ‖(a - b) * u‖ = ‖(ϖ : v.adicCompletion K)‖ ^ m₂) ∧
    (∀ n : ℤ, ‖a - b‖ * ν.real {u : v.adicCompletion K | ‖(a - b) * u‖ ≤ ‖(ϖ : v.adicCompletion K)‖ ^ n} =
      ‖(ϖ : v.adicCompletion K)‖ ^ n * ν.real (v.adicCompletionIntegers K : Set (v.adicCompletion K))) ∧
    (∀ n : ℤ, ‖a - b‖ * ν.real {u : v.adicCompletion K | ‖(a - b) * u‖ = ‖(ϖ : v.adicCompletion K)‖ ^ n} =
      ‖(ϖ : v.adicCompletion K)‖ ^ n * (1 - ‖(ϖ : v.adicCompletion K)‖) *
        ν.real (v.adicCompletionIntegers K : Set (v.adicCompletion K))) ∧
    ‖a - b‖ * ν.real {u : v.adicCompletion K |
        (AutomorphicForm.unipotentGL2 u)⁻¹ * t * AutomorphicForm.unipotentGL2 u ∈
          AutomorphicForm.localIntegralSet K v * ({dl} : Set (GL (Fin 2) (v.adicCompletion K))) *
            AutomorphicForm.localIntegralSet K v} ≤
      ‖(ϖ : v.adicCompletion K)‖ ^ m₂ * ν.real (v.adicCompletionIntegers K : Set (v.adicCompletion K)) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_unipotentGL2_conj_diagonal_mem_doubleCoset_iff_and_norm_sub_mul_measureReal_le.solution
