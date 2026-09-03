import Mathlib
import Theorems.Thm_Subalgebra_isNoetherianRing_and_dimensionLEOne_of_isFractionRing_of_finite
import P2M.Util
namespace P2MW.S_IsNoetherianRing_of_ringKrullDim_le_one_of_finiteDimensional_subalgebra

set_option autoImplicit false

universe u v w

theorem solution
    {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R] (hR : ringKrullDim R ≤ 1)
    (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]
    (L : Type w) [Field L] [Algebra R L] [Algebra K L] [IsScalarTower R K L] [FiniteDimensional K L]
    (B : Subalgebra R L) :
    IsNoetherianRing ↥B ∧ ringKrullDim ↥B ≤ 1 := by
  haveI : Ring.KrullDimLE 1 R := Ring.krullDimLE_iff.mpr hR
  obtain ⟨hN, hD, -⟩ :=
    Subalgebra.isNoetherianRing_and_dimensionLEOne_of_isFractionRing_of_finite (K := K) B
  haveI := hD
  exact ⟨hN, Ring.krullDimLE_iff.mp (inferInstance : Ring.KrullDimLE 1 ↥B)⟩
