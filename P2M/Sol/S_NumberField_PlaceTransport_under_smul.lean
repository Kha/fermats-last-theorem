import Mathlib
import Definitions.Def_NumberField_PlaceTransport
import P2M.Util
namespace P2MW.S_NumberField_PlaceTransport_under_smul

set_option autoImplicit false
open scoped NumberField.PlaceTransport

theorem solution (E K : Type*) [Field E] [Field K] [Algebra E K]
    (σ : K ≃ₐ[E] K) (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    (σ • w).under (NumberField.RingOfIntegers E) = w.under (NumberField.RingOfIntegers E) := by
  apply IsDedekindDomain.HeightOneSpectrum.ext
  rw [IsDedekindDomain.HeightOneSpectrum.under_asIdeal, IsDedekindDomain.HeightOneSpectrum.under_asIdeal]
  ext x
  rw [Ideal.mem_comap, Ideal.mem_comap, NumberField.PlaceTransport.mem_smul_asIdeal_iff]
  have : σ⁻¹ • (algebraMap (NumberField.RingOfIntegers E) (NumberField.RingOfIntegers K) x)
      = algebraMap (NumberField.RingOfIntegers E) (NumberField.RingOfIntegers K) x :=
    Subtype.ext ((σ⁻¹).commutes _)
  rw [this]
