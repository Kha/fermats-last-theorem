import Definitions.Def_CerednikDrinfeld_CosetGraphAtPrime
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_IsOrder_exists_isMaximalOrder_isEichlerOrder_forall_localBox_eq_of_forall_exists_isMaximalOrder_localBox_eq
attribute [-instance] IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions
attribute [-simp] QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open IsDedekindDomain NumberField QuaternionAlgebra CerednikDrinfeld

theorem QuaternionAlgebra.IsOrder.exists_isMaximalOrder_isEichlerOrder_forall_localBox_eq_of_forall_exists_isMaximalOrder_localBox_eq
    {r rbar N : ℕ} [Fact r.Prime] [Fact rbar.Prime] [NeZero N] (hrr : rbar ≠ r) (hrN : ¬ r ∣ N) (hrbarN : ¬ rbar ∣ N)
    (hN : Squarefree N)
    {a₁ b₁ : ℚ} (hdef : IsDefiniteRamifiedExactlyAt a₁ b₁ rbar)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : ((r : ℕ) : 𝓞 ℚ) ∈ v.asIdeal)
    (R : Submodule ℤ ℍ[ℚ, a₁, b₁]) (hR : IsOrder R)

    (Λ₁ : Submodule ℤ ℍ[ℚ, a₁, b₁]) (hΛ₁ : IsMaximalOrder Λ₁)
    (hmax : ∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ v →
      ∃ u : (ℍ[ℚ, a₁, b₁] ⊗[ℚ] w.adicCompletion ℚ)ˣ, ∀ x : ℍ[ℚ, a₁, b₁] ⊗[ℚ] w.adicCompletion ℚ,
        x ∈ Submodule.localBox R w ↔
          ∃ y ∈ Submodule.localBox Λ₁ w,
            x = (u : ℍ[ℚ, a₁, b₁] ⊗[ℚ] w.adicCompletion ℚ) * y * ((u⁻¹ : (ℍ[ℚ, a₁, b₁] ⊗[ℚ] w.adicCompletion ℚ)ˣ) : ℍ[ℚ, a₁, b₁] ⊗[ℚ] w.adicCompletion ℚ))

    (φ : ↥R →ₗ[ℤ] Matrix (Fin 2) (Fin 2) (ZMod N))
    (hφ1 : ∀ h : (1 : ℍ[ℚ, a₁, b₁]) ∈ R, φ ⟨1, h⟩ = 1)
    (hφmul : ∀ (x y : ↥R) (h : (x : ℍ[ℚ, a₁, b₁]) * (y : ℍ[ℚ, a₁, b₁]) ∈ R), φ ⟨(x : ℍ[ℚ, a₁, b₁]) * (y : ℍ[ℚ, a₁, b₁]), h⟩ = φ x * φ y)
    (hφsurj : Function.Surjective φ)
    (hφker : ∀ x : ↥R, φ x = 0 ↔ ∃ y : ↥R, (x : ℍ[ℚ, a₁, b₁]) = (N : ℚ) • (y : ℍ[ℚ, a₁, b₁]))
    (R₀ : Submodule ℤ ℍ[ℚ, a₁, b₁]) (hR₀ : ∀ x : ↥R, (x : ℍ[ℚ, a₁, b₁]) ∈ R₀ ↔ φ x 1 0 = 0) (hR₀R : R₀ ≤ R) :
    ∃ Λ' R' : Submodule ℤ ℍ[ℚ, a₁, b₁], IsMaximalOrder Λ' ∧ IsEichlerOrder R' N ∧ R' ≤ Λ' ∧
      ∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ v →
        Submodule.localBox R' w = Submodule.localBox R₀ w ∧ Submodule.localBox Λ' w = Submodule.localBox R w := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_IsOrder_exists_isMaximalOrder_isEichlerOrder_forall_localBox_eq_of_forall_exists_isMaximalOrder_localBox_eq.solution
