import Mathlib
import P2M.Util
namespace P2MW.S_PowerSeries_ringKrullDim_powerSeries

set_option autoImplicit false

universe u v

open IsLocalRing

namespace Ws14Port
open PowerSeries

variable {R : Type u} [CommRing R]

lemma isSMulRegular_X : IsSMulRegular R⟦X⟧ (X : R⟦X⟧) := by
  intro f g h
  simp only [smul_eq_mul] at h
  ext n
  simpa only [coeff_succ_X_mul] using congrArg (coeff (n + 1)) h

lemma ker_constantCoeff : RingHom.ker (constantCoeff (R := R)) = Ideal.span {(X : R⟦X⟧)} := by
  ext f
  rw [RingHom.mem_ker, Ideal.mem_span_singleton, X_dvd_iff]

noncomputable def quotSpanXEquiv : (R⟦X⟧ ⧸ Ideal.span {(X : R⟦X⟧)}) ≃+* R :=
  (Ideal.quotEquivOfEq ker_constantCoeff.symm).trans
    (RingHom.quotientKerEquivOfSurjective constantCoeff_surj)

lemma X_mem_maximalIdeal [IsLocalRing R] : (X : R⟦X⟧) ∈ maximalIdeal R⟦X⟧ := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro h
  have := (isUnit_iff_constantCoeff (φ := (X : R⟦X⟧))).mp h
  simp at this

end Ws14Port

open PowerSeries in
theorem solution (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R] :
    ringKrullDim (PowerSeries R) = ringKrullDim R + 1 := by
  have h := ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim
    (R := R⟦X⟧) (x := X) Ws14Port.isSMulRegular_X Ws14Port.X_mem_maximalIdeal
  rw [ringKrullDim_eq_of_ringEquiv (Ws14Port.quotSpanXEquiv (R := R))] at h
  exact h.symm
