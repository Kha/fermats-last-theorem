import Mathlib
import Definitions.Def_CerednikDrinfeld_CosetGraphAtPrime
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_exists_units_forall_mem_localBox_iff_of_forall_iff_mem_range_of_isMaximalOrder_of_notMem_of_notMem
attribute [-simp] QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open IsDedekindDomain NumberField QuaternionAlgebra CerednikDrinfeld

theorem QuaternionAlgebra.exists_units_forall_mem_localBox_iff_of_forall_iff_mem_range_of_isMaximalOrder_of_notMem_of_notMem
    {r rbar : ℕ} [Fact r.Prime] [Fact rbar.Prime] (hrr : rbar ≠ r)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b r rbar)
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    {c d : ℚ} (hH' : IsDefiniteRamifiedExactlyAt c d r)
    (O : Submodule ℤ ℍ[ℚ, c, d]) (hO : IsMaximalOrder O)
    {a₁ b₁ : ℚ} (hdef : IsDefiniteRamifiedExactlyAt a₁ b₁ rbar)
    (j : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d]) (hj : ∀ (m : ↥Λ) (i l : Fin 2), j (m : ℍ[ℚ, a, b]) i l ∈ O)
    (τ : ℍ[ℚ, a₁, b₁] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d]) (hτ : Function.Injective τ)
    (hτc : ∀ y : Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d], (∀ m : ℍ[ℚ, a, b], y * j m = j m * y) ↔ y ∈ Set.range τ)
    (R : Submodule ℤ ℍ[ℚ, a₁, b₁]) (hRiff : ∀ x : ℍ[ℚ, a₁, b₁], x ∈ R ↔ ∀ i l : Fin 2, τ x i l ∈ O)
    (Λ₁ : Submodule ℤ ℍ[ℚ, a₁, b₁]) (hΛ₁ : IsMaximalOrder Λ₁)
    (w : HeightOneSpectrum (𝓞 ℚ)) (hrw : ((r : ℕ) : 𝓞 ℚ) ∉ w.asIdeal) (hrbw : ((rbar : ℕ) : 𝓞 ℚ) ∉ w.asIdeal) :
    ∃ u : (ℍ[ℚ, a₁, b₁] ⊗[ℚ] w.adicCompletion ℚ)ˣ, ∀ x : ℍ[ℚ, a₁, b₁] ⊗[ℚ] w.adicCompletion ℚ,
      x ∈ Submodule.localBox R w ↔
        ∃ y ∈ Submodule.localBox Λ₁ w,
          x = (u : ℍ[ℚ, a₁, b₁] ⊗[ℚ] w.adicCompletion ℚ) * y * ((u⁻¹ : (ℍ[ℚ, a₁, b₁] ⊗[ℚ] w.adicCompletion ℚ)ˣ) : ℍ[ℚ, a₁, b₁] ⊗[ℚ] w.adicCompletion ℚ) := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_exists_units_forall_mem_localBox_iff_of_forall_iff_mem_range_of_isMaximalOrder_of_notMem_of_notMem.solution
