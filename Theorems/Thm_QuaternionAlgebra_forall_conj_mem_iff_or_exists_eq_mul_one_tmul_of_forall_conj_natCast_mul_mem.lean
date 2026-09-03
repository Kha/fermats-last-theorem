import Mathlib
import Definitions.Def_Submodule_LocalBox
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_forall_conj_mem_iff_or_exists_eq_mul_one_tmul_of_forall_conj_natCast_mul_mem
attribute [-simp] LocalGL2.swapUnit_val

set_option autoImplicit false

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField

theorem QuaternionAlgebra.forall_conj_mem_iff_or_exists_eq_mul_one_tmul_of_forall_conj_natCast_mul_mem
    {a b : ℚ} (v : HeightOneSpectrum (𝓞 ℚ)) (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓv : (ℓ : 𝓞 ℚ) ∈ v.asIdeal)
    (φ : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ ≃+* Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))
    (hφ : ∀ r : v.adicCompletion ℚ,
      φ ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] r) = r • (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)))
    (h : GL (Fin 2) (v.adicCompletion ℚ))
    (O : AddSubgroup (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ))
    (hO : ∀ x, x ∈ O ↔ ∀ i j,
      (((h⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) *
        φ x * (h : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))) i j ∈ v.adicCompletionIntegers ℚ)
    (ν : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ)
    (hν : ∀ y ∈ O, ((ν⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) *
      (((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (ℓ : v.adicCompletion ℚ)) * y) * ν ∈ O) :
    (∀ y : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ,
        ((ν⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) * y * ν ∈ O ↔
          y ∈ O) ∨
      ∃ (s : v.adicCompletion ℚ) (ν₀ : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ),
        (ν : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) = ν₀ * ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] s) ∧
        (ν₀ : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) ∈ O ∧
        ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (ℓ : v.adicCompletion ℚ)) *
          ((ν₀⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) ∈ O ∧
        ((ν₀⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) ∉ O ∧
        ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (ℓ : v.adicCompletion ℚ)⁻¹) * (ν₀ : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) ∉ O := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_forall_conj_mem_iff_or_exists_eq_mul_one_tmul_of_forall_conj_natCast_mul_mem.solution
