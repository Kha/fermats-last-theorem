import Mathlib
import Definitions.Def_QuaternionAlgebra_ClassSetHecke
import Definitions.Def_Submodule_LocalBox
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_IsOrder_exists_mem_primeHeckeSet_eq_ofFiniteIdele_mul_iff
attribute [-instance] IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions

set_option autoImplicit false

open scoped TensorProduct Quaternion Pointwise
open IsDedekindDomain NumberField

theorem QuaternionAlgebra.IsOrder.exists_mem_primeHeckeSet_eq_ofFiniteIdele_mul_iff {a b : ℚ}
    {R : Submodule ℤ ℍ[ℚ, a, b]} (hR : QuaternionAlgebra.IsOrder R) {ℓ : ℕ} (hℓ : ℓ.Prime)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : (ℓ : 𝓞 ℚ) ∈ v.asIdeal)
    (φ : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ ≃+* Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))
    (hφ : ∀ r : v.adicCompletion ℚ,
      φ ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] r) = r • (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)))
    (hRv : ∀ z : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ,
      z ∈ Submodule.localBox R v ↔ ∀ i j, φ z i j ∈ v.adicCompletionIntegers ℚ)
    (x : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (J : Submodule ℤ ℍ[ℚ, a, b]) :
    (∃ h ∈ QuaternionAlgebra.primeHeckeSet R ℓ, J = Submodule.ofFiniteIdele R (x * h)) ↔
      (J ≤ Submodule.ofFiniteIdele R x ∧
        (∀ z ∈ Submodule.ofFiniteIdele R x, (ℓ : ℚ) • z ∈ J) ∧
        (∃ y : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ, J = Submodule.ofFiniteIdele R y) ∧
        J.toAddSubgroup.relIndex (Submodule.ofFiniteIdele R x).toAddSubgroup = ℓ ^ 2) := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_IsOrder_exists_mem_primeHeckeSet_eq_ofFiniteIdele_mul_iff.solution
