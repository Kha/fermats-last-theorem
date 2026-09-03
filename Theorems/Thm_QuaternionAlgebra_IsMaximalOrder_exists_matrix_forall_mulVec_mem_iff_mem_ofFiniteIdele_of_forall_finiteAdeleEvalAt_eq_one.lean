import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_Submodule_LocalBox
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_IsMaximalOrder_exists_matrix_forall_mulVec_mem_iff_mem_ofFiniteIdele_of_forall_finiteAdeleEvalAt_eq_one
attribute [-simp] QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul

set_option autoImplicit false

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField QuaternionAlgebra

theorem QuaternionAlgebra.IsMaximalOrder.exists_matrix_forall_mulVec_mem_iff_mem_ofFiniteIdele_of_forall_finiteAdeleEvalAt_eq_one
    {c d : ℚ} (q : ℕ) [Fact q.Prime] (hH : IsDefiniteRamifiedExactlyAt c d q)
    (O : Submodule ℤ ℍ[ℚ, c, d]) (hO : IsMaximalOrder O)
    (r : ℕ) [Fact r.Prime] (hrq : r ≠ q) (v : HeightOneSpectrum (𝓞 ℚ)) (hv : ((r : ℕ) : 𝓞 ℚ) ∈ v.asIdeal)
    (g₁ g₂ : (ℍ[ℚ, c, d] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hg₁ : ∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ v →
      Submodule.finiteAdeleEvalAt ℍ[ℚ, c, d] w (g₁ : ℍ[ℚ, c, d] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) = 1)
    (hg₂ : ∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ v →
      Submodule.finiteAdeleEvalAt ℍ[ℚ, c, d] w (g₂ : ℍ[ℚ, c, d] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) = 1)
    (hdet : ∀ φ : ℍ[ℚ, c, d] ⊗[ℚ] v.adicCompletion ℚ ≃+* Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ),
      (∀ t : v.adicCompletion ℚ,
        φ ((1 : ℍ[ℚ, c, d]) ⊗ₜ[ℚ] t) = t • (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))) →
      (∀ x : ℍ[ℚ, c, d] ⊗[ℚ] v.adicCompletion ℚ,
        x ∈ Submodule.localBox O v ↔ ∀ i j, φ x i j ∈ v.adicCompletionIntegers ℚ) →
      (φ (Submodule.finiteAdeleEvalAt ℍ[ℚ, c, d] v
          ((g₁ * g₂ : (ℍ[ℚ, c, d] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
            ℍ[ℚ, c, d] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ))).det ∈ v.adicCompletionIntegers ℚ ∧
      (φ (Submodule.finiteAdeleEvalAt ℍ[ℚ, c, d] v
          (((g₁ * g₂)⁻¹ : (ℍ[ℚ, c, d] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
            ℍ[ℚ, c, d] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ))).det ∈ v.adicCompletionIntegers ℚ) :
    ∃ γ γ' : Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d], γ * γ' = 1 ∧ γ' * γ = 1 ∧
      ∀ x : Fin 2 → ℍ[ℚ, c, d],
        (∀ i, (γ'.mulVec x) i ∈ O) ↔
          (x 0 ∈ Submodule.ofFiniteIdele O g₁ ∧ x 1 ∈ Submodule.ofFiniteIdele O g₂) := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_IsMaximalOrder_exists_matrix_forall_mulVec_mem_iff_mem_ofFiniteIdele_of_forall_finiteAdeleEvalAt_eq_one.solution
