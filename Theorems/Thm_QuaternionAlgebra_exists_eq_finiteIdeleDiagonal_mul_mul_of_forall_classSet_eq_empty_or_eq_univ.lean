import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_Submodule_LocalBox
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_exists_eq_finiteIdeleDiagonal_mul_mul_of_forall_classSet_eq_empty_or_eq_univ
attribute [-instance] IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions
attribute [-simp] QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul

set_option autoImplicit false
open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField QuaternionAlgebra CerednikDrinfeld

theorem QuaternionAlgebra.exists_eq_finiteIdeleDiagonal_mul_mul_of_forall_classSet_eq_empty_or_eq_univ
    {a b : ℚ} (R : Submodule ℤ ℍ[ℚ, a, b]) (hR : IsOrder R)
    (r : ℕ) [Fact r.Prime] (v : HeightOneSpectrum (𝓞 ℚ)) (hv : ((r : ℕ) : 𝓞 ℚ) ∈ v.asIdeal)
    (n : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (hn : n ∈ primeHeckeSet R r)
    (hconn : ∀ P : Set (ClassSet (Submodule.finiteIdeleStabilizer R)),
      (∀ e : ClassSet (Submodule.finiteIdeleStabilizer (meetOrder R n)),
        (classSetDegeneracyData R n).a e ∈ P ↔ (classSetDegeneracyData R n).b e ∈ P) →
      P = ∅ ∨ P = Set.univ)
    (x : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
    ∃ (γ : (ℍ[ℚ, a, b])ˣ) (g u : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ),
      u ∈ Submodule.finiteIdeleStabilizer R ∧
      (∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ v →
        Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w (g : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) = 1) ∧
      x = Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] γ * g * u := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_exists_eq_finiteIdeleDiagonal_mul_mul_of_forall_classSet_eq_empty_or_eq_univ.solution
