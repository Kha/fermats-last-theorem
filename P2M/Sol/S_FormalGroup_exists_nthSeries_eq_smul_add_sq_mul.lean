import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Theorems.Thm_FormalGroup_coeff_one_nthSeries
import P2M.Util
namespace P2MW.S_FormalGroup_exists_nthSeries_eq_smul_add_sq_mul

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 6400000

section
section

open MvPowerSeries IsLocalRing

noncomputable section

namespace FormalGroup
p2m_export "FormalGroup" "nthSeries constantCoeff_nthSeries coeff_one_nthSeries"
p2m_open "FormalGroup"

variable {R : Type*} [CommRing R]
variable {A : Type*} [CommRing A] [UniformSpace A] [Algebra R A]

theorem exists_nthSeries_eq_smul_add_sq_mul_s18 (F : FormalGroup R) (n : ℕ) :
    ∃ G : PowerSeries R, F.nthSeries n
      = (n : R) • PowerSeries.X + PowerSeries.X ^ 2 * G := by
  have hdvd : (PowerSeries.X : PowerSeries R) ^ 2
      ∣ (F.nthSeries n - (n : R) • PowerSeries.X) := by
    rw [PowerSeries.X_pow_dvd_iff]
    intro m hm
    interval_cases m
    · rw [map_sub, PowerSeries.coeff_zero_eq_constantCoeff_apply, F.constantCoeff_nthSeries,
        PowerSeries.coeff_smul, PowerSeries.coeff_zero_X, smul_zero, sub_zero]
    · rw [map_sub, F.coeff_one_nthSeries, PowerSeries.coeff_smul, PowerSeries.coeff_one_X,
        smul_eq_mul, mul_one, sub_self]
  obtain ⟨G, hG⟩ := hdvd
  refine ⟨G, ?_⟩
  rw [← hG]
  ring

end FormalGroup

end

end

end

theorem solution {R : Type*} [CommRing R] (F : FormalGroup R) (n : ℕ) :
    ∃ G : PowerSeries R, F.nthSeries n = (n : R) • PowerSeries.X + PowerSeries.X ^ 2 * G :=
  FormalGroup.exists_nthSeries_eq_smul_add_sq_mul_s18 F n
