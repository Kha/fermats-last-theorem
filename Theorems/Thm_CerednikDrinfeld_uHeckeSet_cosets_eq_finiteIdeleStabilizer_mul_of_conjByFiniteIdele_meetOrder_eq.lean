import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_uHeckeSet_cosets_eq_finiteIdeleStabilizer_mul_of_conjByFiniteIdele_meetOrder_eq
attribute [-instance] CerednikDrinfeld.CosetGraph.projGraphAction CerednikDrinfeld.CosetGraph.projVertMulAction CerednikDrinfeld.CosetGraph.awayVertMulAction CerednikDrinfeld.CosetGraph.actionKer_normal CerednikDrinfeld.CosetGraph.vertMulAction CerednikDrinfeld.Mumford.dartAction IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions
attribute [-simp] QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul LocalGL2.swapUnit_val

set_option autoImplicit false

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField QuaternionAlgebra CerednikDrinfeld

theorem CerednikDrinfeld.uHeckeSet_cosets_eq_finiteIdeleStabilizer_mul_of_conjByFiniteIdele_meetOrder_eq
    {a b : ℚ} (R : Submodule ℤ ℍ[ℚ, a, b]) {N : ℕ} (q : ℕ) [Fact q.Prime]
    (n : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hR : IsEichlerOrder R N) (hqN : ¬ q ∣ N) {q' : ℕ} [Fact q'.Prime] (hqq' : q' ≠ q)
    (hdef : IsDefiniteRamifiedExactlyAt a b q') (hnH : n ∈ primeHeckeSet R q)
    (hn : IsEichlerOrder (meetOrder R n) (N * q))
    (hnorm : Submodule.conjByFiniteIdele (meetOrder R n) n = meetOrder R n) :
    (∀ u : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ,
        u ∈ Submodule.finiteIdeleStabilizer (meetOrder R n) ↔
          n * u * n⁻¹ ∈ Submodule.finiteIdeleStabilizer (meetOrder R n)) ∧
    (∀ h ∈ uHeckeSet R n q, ∃ u ∈ Submodule.finiteIdeleStabilizer R,
        u ∉ Submodule.finiteIdeleStabilizer (meetOrder R n) ∧
          h⁻¹ * (u * n) ∈ Submodule.finiteIdeleStabilizer (meetOrder R n)) ∧
    (∀ u ∈ Submodule.finiteIdeleStabilizer R, u ∉ Submodule.finiteIdeleStabilizer (meetOrder R n) →
        ∃ h ∈ uHeckeSet R n q, h⁻¹ * (u * n) ∈ Submodule.finiteIdeleStabilizer (meetOrder R n)) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_uHeckeSet_cosets_eq_finiteIdeleStabilizer_mul_of_conjByFiniteIdele_meetOrder_eq.solution
