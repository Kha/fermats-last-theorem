import Mathlib
import Definitions.Def_CerednikDrinfeld_CosetGraphAtPrime
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_IsMaximalOrder_exists_isUnit_forall_mem_iff_exists_mem_localBox_eq_mul_of_forall_isUnit
attribute [-simp] QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open IsDedekindDomain NumberField QuaternionAlgebra CerednikDrinfeld

theorem QuaternionAlgebra.IsMaximalOrder.exists_isUnit_forall_mem_iff_exists_mem_localBox_eq_mul_of_forall_isUnit
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsMaximalOrder Λ)
    (w : HeightOneSpectrum (𝓞 ℚ)) (hdiv : ∀ x : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ, x ≠ 0 → IsUnit x)
    {p : ℕ} [Fact p.Prime] (hpw : ((p : ℕ) : 𝓞 ℚ) ∈ w.asIdeal)
    (M : AddSubgroup (ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)) (hM0 : ∃ x ∈ M, x ≠ 0)
    (hleft : ∀ d ∈ Submodule.localBox Λ w, ∀ x ∈ M, d * x ∈ M)
    (hbdd : ∃ n : ℕ, ∀ x ∈ M, ((p : ℕ) : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ) ^ n * x ∈ Submodule.localBox Λ w) :
    ∃ x₀ ∈ M, IsUnit x₀ ∧ ∀ x : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ, x ∈ M ↔ ∃ d ∈ Submodule.localBox Λ w, x = d * x₀ := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_IsMaximalOrder_exists_isUnit_forall_mem_iff_exists_mem_localBox_eq_mul_of_forall_isUnit.solution
