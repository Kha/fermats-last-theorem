import Mathlib
import Definitions.Def_NumberField_PlaceTransport
import Definitions.Def_NumberField_PlaceDecompositionAction
import P2M.Util
namespace P2MW.S_NumberField_PlaceTransport_stabilizer_eq_decomp

set_option autoImplicit false
open scoped NumberField.PlaceTransport
open scoped Pointwise

theorem solution (E K : Type*) [Field E] [Field K] [NumberField K] [Algebra E K]
    (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    MulAction.stabilizer (K ≃ₐ[E] K) w = NumberField.PlaceDecomp.decomp E K w := by
  ext σ
  rw [MulAction.mem_stabilizer_iff]
  constructor
  · intro h

    rw [MulAction.mem_stabilizer_iff]
    ext x
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, Valuation.mem_valuationSubring_iff,
      Valuation.mem_valuationSubring_iff, show σ⁻¹ • x = σ⁻¹ x from rfl,
      NumberField.PlaceTransport.valuation_apply_of_smul_eq (NumberField.PlaceTransport.inv_smul_eq_of_smul_eq h)]
  · intro hσ

    have hσ' : σ⁻¹ ∈ NumberField.PlaceDecomp.decomp E K w := inv_mem hσ
    apply IsDedekindDomain.HeightOneSpectrum.ext
    ext x
    rw [NumberField.PlaceTransport.mem_smul_asIdeal_iff,
      ← IsDedekindDomain.HeightOneSpectrum.intValuation_lt_one_iff_mem,
      ← IsDedekindDomain.HeightOneSpectrum.intValuation_lt_one_iff_mem]
    have key : w.intValuation (σ⁻¹ • x) = w.intValuation x := by
      rw [← IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap (K := K),
        ← IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap (K := K)]
      exact NumberField.PlaceDecomp.valuation_apply_of_mem σ⁻¹ hσ' (algebraMap _ K x)
    exact Iff.of_eq (congrArg (· < (1 : WithZero (Multiplicative ℤ))) key)
