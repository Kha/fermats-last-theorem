import Mathlib
import Definitions.Def_LaurentSeries_HeckeU
import Definitions.Def_LaurentSeries_HeckeV
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_LaurentCoeff
import P2M.Util
namespace P2MW.S_LaurentSeries_commute_heckeU_heckeV

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

set_option autoImplicit false

open ModularCurve LaurentSeries

theorem solution (R : Type*) [CommRing R] (p ℓ : ℕ) (hp : 0 < p) (hℓ : 0 < ℓ)
    (hpl : Nat.Coprime p ℓ) :
    Commute (heckeU R p hp) (heckeV R ℓ hℓ)  := by
  have cop : IsCoprime (ℓ : ℤ) (p : ℤ) := Nat.isCoprime_iff_coprime.mpr hpl.symm
  have hℓ0 : (ℓ : ℤ) ≠ 0 := by exact_mod_cast hℓ.ne'
  ext f n
  simp only [Module.End.mul_apply, coeff_heckeU, coeff_heckeV]
  by_cases h : (ℓ : ℤ) ∣ n
  · obtain ⟨m, rfl⟩ := h
    rw [if_pos ⟨p * m, by ring⟩, if_pos ⟨m, rfl⟩, show (p : ℤ) * (ℓ * m) = ℓ * (p * m) by ring,
      Int.mul_ediv_cancel_left _ hℓ0, Int.mul_ediv_cancel_left _ hℓ0]
  · rw [if_neg h, if_neg]
    intro h'
    exact h (cop.dvd_of_dvd_mul_left h')
