import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_Submodule_LocalBox
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_IsMaximalOrder_exists_units_forall_mem_iff_mem_ofFiniteIdele_of_forall_mul_mem
attribute [-simp] QuaternionAlgebra.nrd_coe QuaternionAlgebra.nrd_one QuaternionAlgebra.trd_mk QuaternionAlgebra.nrd_mk QuaternionAlgebra.nrd_neg QuaternionAlgebra.nrd_zero QuaternionAlgebra.nrd_star QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul LocalGL2.swapUnit_val

set_option autoImplicit false

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField QuaternionAlgebra

theorem QuaternionAlgebra.IsMaximalOrder.exists_units_forall_mem_iff_mem_ofFiniteIdele_of_forall_mul_mem
    {c d : ℚ} (q : ℕ) [Fact q.Prime] (hH : IsDefiniteRamifiedExactlyAt c d q)
    (O : Submodule ℤ ℍ[ℚ, c, d]) (hO : IsMaximalOrder O)
    (r : ℕ) [Fact r.Prime] (hrq : r ≠ q) (v : HeightOneSpectrum (𝓞 ℚ)) (hv : ((r : ℕ) : 𝓞 ℚ) ∈ v.asIdeal)
    (I : Submodule ℤ ℍ[ℚ, c, d]) (hIO : I ≤ O) (hmul : ∀ z ∈ I, ∀ o ∈ O, z * o ∈ I)
    (hfull : ∃ n : ℤ, n ≠ 0 ∧ ∀ o ∈ O, n • o ∈ I) :
    ∃ (β : (ℍ[ℚ, c, d])ˣ) (g : (ℍ[ℚ, c, d] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ),
      (∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ v →
        Submodule.finiteAdeleEvalAt ℍ[ℚ, c, d] w (g : ℍ[ℚ, c, d] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) = 1) ∧
      (∀ φ : ℍ[ℚ, c, d] ⊗[ℚ] v.adicCompletion ℚ ≃+* Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ),
        (∀ t : v.adicCompletion ℚ,
          φ ((1 : ℍ[ℚ, c, d]) ⊗ₜ[ℚ] t) = t • (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))) →
        (∀ x : ℍ[ℚ, c, d] ⊗[ℚ] v.adicCompletion ℚ,
          x ∈ Submodule.localBox O v ↔ ∀ i j, φ x i j ∈ v.adicCompletionIntegers ℚ) →
        (φ (Submodule.finiteAdeleEvalAt ℍ[ℚ, c, d] v
            (g : ℍ[ℚ, c, d] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ))).det ∈ v.adicCompletionIntegers ℚ ∧
        (φ (Submodule.finiteAdeleEvalAt ℍ[ℚ, c, d] v
            ((g⁻¹ : (ℍ[ℚ, c, d] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
              ℍ[ℚ, c, d] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ))).det ∈ v.adicCompletionIntegers ℚ) ∧
      ∀ z : ℍ[ℚ, c, d], z ∈ I ↔ ((β⁻¹ : (ℍ[ℚ, c, d])ˣ) : ℍ[ℚ, c, d]) * z ∈ Submodule.ofFiniteIdele O g := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_IsMaximalOrder_exists_units_forall_mem_iff_mem_ofFiniteIdele_of_forall_mul_mem.solution
