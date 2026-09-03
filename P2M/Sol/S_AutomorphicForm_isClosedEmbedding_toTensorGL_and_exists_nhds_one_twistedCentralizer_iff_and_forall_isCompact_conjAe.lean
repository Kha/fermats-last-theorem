import Definitions.Def_AutomorphicForm_TwistedOrbital
import Theorems.Thm_AutomorphicForm_isClosedEmbedding_toTensorGL_and_exists_nhds_one_mem_twistedCentralizer_conjAe_iff
import Theorems.Thm_AutomorphicForm_exists_nhds_one_forall_isCompact_exists_eq_toTensorGL_mul_of_conjAe_twistedConj_mem
import P2M.Util
namespace P2MW.S_AutomorphicForm_isClosedEmbedding_toTensorGL_and_exists_nhds_one_twistedCentralizer_iff_and_forall_isCompact_conjAe

set_option autoImplicit false

open MeasureTheory AutomorphicForm
open scoped TensorProduct TensorProduct.RightActions

theorem solution
    (d : ℝˣ) :
    Topology.IsClosedEmbedding (toTensorGL ℝ ℂ ℝ) ∧
    ∃ U ∈ nhds (1 : GL (Fin 2) ℝ),
      (∀ t ∈ U, ∀ x : GL (Fin 2) (ℂ ⊗[ℝ] ℝ),
        x ∈ twistedCentralizer ℝ ℂ ℝ Complex.conjAe
            (toTensorGL ℝ ℂ ℝ (t * Matrix.GeneralLinearGroup.scalar (Fin 2) d)) ↔
          ∃ m : GL (Fin 2) ℝ, m ∈ Subgroup.centralizer ({t} : Set (GL (Fin 2) ℝ)) ∧ x = toTensorGL ℝ ℂ ℝ m) ∧
      ∀ C : Set (GL (Fin 2) ℂ), IsCompact C →
        ∃ K : Set (GL (Fin 2) (ℂ ⊗[ℝ] ℝ)), IsCompact K ∧
          ∀ t ∈ U, ∀ x : GL (Fin 2) (ℂ ⊗[ℝ] ℝ),
            (Matrix.GeneralLinearGroup.map
              (@AlgEquiv.toRingEquiv ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _
                (Algebra.TensorProduct.rid ℝ ℝ ℂ)).toRingHom
              (x⁻¹ * toTensorGL ℝ ℂ ℝ (t * Matrix.GeneralLinearGroup.scalar (Fin 2) d) *
                sigmaGL ℝ ℂ ℝ Complex.conjAe x) : GL (Fin 2) ℂ) ∈ C →
              ∃ (m : GL (Fin 2) ℝ) (k : GL (Fin 2) (ℂ ⊗[ℝ] ℝ)), k ∈ K ∧ x = toTensorGL ℝ ℂ ℝ m * k := by
  obtain ⟨hce, U₁, hU₁, h₁⟩ := AutomorphicForm.isClosedEmbedding_toTensorGL_and_exists_nhds_one_mem_twistedCentralizer_conjAe_iff d
  obtain ⟨U₂, hU₂, h₂⟩ := AutomorphicForm.exists_nhds_one_forall_isCompact_exists_eq_toTensorGL_mul_of_conjAe_twistedConj_mem d
  refine ⟨hce, U₁ ∩ U₂, Filter.inter_mem hU₁ hU₂, fun t ht => h₁ t ht.1, fun C hC => ?_⟩
  obtain ⟨K, hK, hK'⟩ := h₂ C hC
  exact ⟨K, hK, fun t ht => hK' t ht.2⟩
