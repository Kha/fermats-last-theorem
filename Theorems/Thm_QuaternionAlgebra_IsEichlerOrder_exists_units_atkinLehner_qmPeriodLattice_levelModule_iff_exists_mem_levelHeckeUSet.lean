import Definitions.Def_QuaternionAlgebra_QMPeriodLattice
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_IsEichlerOrder_exists_units_atkinLehner_qmPeriodLattice_levelModule_iff_exists_mem_levelHeckeUSet
attribute [-instance] IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions
attribute [-simp] LocalGL2.swapUnit_val QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul

set_option autoImplicit false

open scoped Quaternion TensorProduct NumberField MatrixGroups Pointwise
open IsDedekindDomain NumberField QuaternionAlgebra CerednikDrinfeld

theorem QuaternionAlgebra.IsEichlerOrder.exists_units_atkinLehner_qmPeriodLattice_levelModule_iff_exists_mem_levelHeckeUSet
    {N q q' : ℕ} [NeZero N] [Fact q.Prime] [Fact q'.Prime] (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N) (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (hN : Squarefree N) (R : Submodule ℤ ℍ[ℚ, a, b]) (hR : IsEichlerOrder R N) (hRΛ : R ≤ Λ)
    (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ) (hι : Function.Injective ι)
    (J' : Submodule ℤ ℍ[ℚ, a, b])
    (hJ' : Λ ≤ J' ∧ (∀ x ∈ Λ, ∀ y ∈ J', x * y ∈ J') ∧ (∀ y ∈ J', ((N : ℤ) • y) ∈ Λ) ∧
      Λ.toAddSubgroup.relIndex J'.toAddSubgroup = N ^ 2 ∧ (∀ x ∈ Λ, x ∈ R ↔ ∀ y ∈ J', y * x ∈ J')) :
    ∃ (wN : (ℍ[ℚ, a, b])ˣ) (g : GL (Fin 2) ℝ),

      (g : Matrix (Fin 2) (Fin 2) ℝ) = ι (wN : ℍ[ℚ, a, b]) ∧ 0 < g.det.val ∧

      (∀ x : ℍ[ℚ, a, b], x ∈ R ↔ (wN : ℍ[ℚ, a, b]) * x * ((wN⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) ∈ R) ∧
      (∀ x : ℍ[ℚ, a, b], nrd ((wN : ℍ[ℚ, a, b]) * x * ((wN⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b])) = nrd x) ∧

      (∀ γ : GL (Fin 2) ℝ, γ ∈ fuchsianGroup R ι ↔ g * γ * g⁻¹ ∈ fuchsianGroup R ι) ∧

      (∀ u : ℍ[ℚ, a, b], IsUnitOf R u → nrd u = 1 →
        ∃ γ : GL (Fin 2) ℝ, γ ∈ fuchsianGroup R ι ∧ (γ : Matrix (Fin 2) (Fin 2) ℝ) = ι u) ∧

      (∀ (ℓ : ℕ), ℓ.Prime → ℓ ≠ q → ℓ ≠ q' → ∀ (τ : UpperHalfPlane) (t : ℍ[ℚ, a, b]), t ∈ R → nrd t = (ℓ : ℚ) →
        ((∀ v : Fin 2 → ℂ, (∃ w ∈ qmPeriodLattice ι J' τ, ∃ y ∈ Λ, (ℓ : ℂ) • w + qmPeriodMap ι τ (y * t) = v) ↔
            ∃ y ∈ J', qmPeriodMap ι τ (y * t) = v) ↔
          ∃ h ∈ (if ℓ ∣ N then levelHeckeUSet Λ R ℓ else primeHeckeSet R ℓ),
            (h : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) =
              ((wN : ℍ[ℚ, a, b]) * t * ((wN⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b])) ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ))) := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_IsEichlerOrder_exists_units_atkinLehner_qmPeriodLattice_levelModule_iff_exists_mem_levelHeckeUSet.solution
