import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_AutomorphicForm_LocalWeightedOrbital
import P2M.Util
import P2M.Sol.S_AutomorphicForm_localHaar_setOf_unipotentGL2_mul_eq_relIndex_and_setIntegral_weight_eq_of_norm_eq_inv

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain

theorem AutomorphicForm.localHaar_setOf_unipotentGL2_mul_eq_relIndex_and_setIntegral_weight_eq_of_norm_eq_inv
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (Λ : AddSubgroup (v.adicCompletion K)) (ϖ : v.adicCompletion K)
    (hϖ : ‖ϖ‖ = (Ideal.absNorm v.asIdeal : ℝ)⁻¹) (m : ℕ)
    (hfin : ∀ s ≤ m, (v.adicCompletionIntegers K).toAddSubgroup.relIndex
      (Λ ⊓ (v.adicCompletionIntegers K).toAddSubgroup.comap (AddMonoidHom.mulLeft (ϖ ^ s))) ≠ 0) :
    (∀ s ≤ m, AutomorphicForm.localHaar K v
        {x | ∃ (y : v.adicCompletion K) (k : GL (Fin 2) (v.adicCompletion K)),
          (y ∈ Λ ∧ ϖ ^ s * y ∈ v.adicCompletionIntegers K) ∧ k ∈ AutomorphicForm.localIntegralSet K v ∧
            x = AutomorphicForm.unipotentGL2 y * k} =
      (v.adicCompletionIntegers K).toAddSubgroup.relIndex
        (Λ ⊓ (v.adicCompletionIntegers K).toAddSubgroup.comap (AddMonoidHom.mulLeft (ϖ ^ s)))) ∧
    (∫ x in {x | ∃ (y : v.adicCompletion K) (k : GL (Fin 2) (v.adicCompletion K)),
          (y ∈ Λ ∧ ϖ ^ m * y ∈ v.adicCompletionIntegers K) ∧ k ∈ AutomorphicForm.localIntegralSet K v ∧
            x = AutomorphicForm.unipotentGL2 y * k},
        AutomorphicForm.LocalWeight.weight x ∂(AutomorphicForm.localHaar K v)) =
      2 * Real.log (Ideal.absNorm v.asIdeal) *
        ∑ s ∈ Finset.range m, ((s + 1 : ℕ) : ℝ) *
          (((v.adicCompletionIntegers K).toAddSubgroup.relIndex
              (Λ ⊓ (v.adicCompletionIntegers K).toAddSubgroup.comap (AddMonoidHom.mulLeft (ϖ ^ (s + 1)))) : ℝ) -
            ((v.adicCompletionIntegers K).toAddSubgroup.relIndex
              (Λ ⊓ (v.adicCompletionIntegers K).toAddSubgroup.comap (AddMonoidHom.mulLeft (ϖ ^ s))) : ℝ)) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_localHaar_setOf_unipotentGL2_mul_eq_relIndex_and_setIntegral_weight_eq_of_norm_eq_inv.solution
