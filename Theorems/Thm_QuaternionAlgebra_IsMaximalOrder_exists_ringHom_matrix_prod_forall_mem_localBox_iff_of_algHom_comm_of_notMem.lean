import Mathlib
import Definitions.Def_CerednikDrinfeld_CosetGraphAtPrime
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_IsMaximalOrder_exists_ringHom_matrix_prod_forall_mem_localBox_iff_of_algHom_comm_of_notMem
attribute [-simp] QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open IsDedekindDomain NumberField QuaternionAlgebra CerednikDrinfeld

theorem QuaternionAlgebra.IsMaximalOrder.exists_ringHom_matrix_prod_forall_mem_localBox_iff_of_algHom_comm_of_notMem
    {r : ℕ} [Fact r.Prime]
    {c d : ℚ} (hH' : IsDefiniteRamifiedExactlyAt c d r)
    (O : Submodule ℤ ℍ[ℚ, c, d]) (hO : IsMaximalOrder O)
    {a b : ℚ} (j : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d])
    {a₁ b₁ : ℚ} (τ : ℍ[ℚ, a₁, b₁] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d]) (hτ : Function.Injective τ)
    (hτj : ∀ (x : ℍ[ℚ, a₁, b₁]) (m : ℍ[ℚ, a, b]), τ x * j m = j m * τ x)
    (R : Submodule ℤ ℍ[ℚ, a₁, b₁]) (hRiff : ∀ x : ℍ[ℚ, a₁, b₁], x ∈ R ↔ ∀ i l : Fin 2, τ x i l ∈ O)
    (w : HeightOneSpectrum (𝓞 ℚ)) (hrw : ((r : ℕ) : 𝓞 ℚ) ∉ w.asIdeal) :
    ∃ (τK : ℍ[ℚ, a₁, b₁] ⊗[ℚ] w.adicCompletion ℚ →+* Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) (w.adicCompletion ℚ))
      (jK : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ →+* Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) (w.adicCompletion ℚ)),
      (∀ c' : w.adicCompletion ℚ, τK ((1 : ℍ[ℚ, a₁, b₁]) ⊗ₜ[ℚ] c') = c' • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) (w.adicCompletion ℚ))) ∧
      (∀ c' : w.adicCompletion ℚ, jK ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] c') = c' • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) (w.adicCompletion ℚ))) ∧
      Function.Injective τK ∧
      (∀ (x : ℍ[ℚ, a₁, b₁] ⊗[ℚ] w.adicCompletion ℚ) (y : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ), τK x * jK y = jK y * τK x) ∧
      (∀ (m : ℍ[ℚ, a, b]) (c' : w.adicCompletion ℚ), (∀ i l : Fin 2, j m i l ∈ O) → c' ∈ w.adicCompletionIntegers ℚ →
        ∀ I J : Fin 2 × Fin 2, jK (m ⊗ₜ[ℚ] c') I J ∈ w.adicCompletionIntegers ℚ) ∧
      (∀ x : ℍ[ℚ, a₁, b₁] ⊗[ℚ] w.adicCompletion ℚ,
        x ∈ Submodule.localBox R w ↔ ∀ I J : Fin 2 × Fin 2, τK x I J ∈ w.adicCompletionIntegers ℚ) := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_IsMaximalOrder_exists_ringHom_matrix_prod_forall_mem_localBox_iff_of_algHom_comm_of_notMem.solution
