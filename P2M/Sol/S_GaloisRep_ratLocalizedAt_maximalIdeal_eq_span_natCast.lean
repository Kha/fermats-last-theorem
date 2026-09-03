import Mathlib
import Definitions.Def_GaloisRep_Flat
import Theorems.Thm_GaloisRep_isLocalization_ratLocalizedAt
import P2M.Util
namespace P2MW.S_GaloisRep_ratLocalizedAt_maximalIdeal_eq_span_natCast
open NumberField
open scoped NumberField

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000
set_option Elab.async false

theorem solution (ℓ : ℕ) (hℓ : ℓ.Prime)
    [IsLocalRing (GaloisRep.ratLocalizedAt ℓ)] :
    IsLocalRing.maximalIdeal (GaloisRep.ratLocalizedAt ℓ) =
      Ideal.span {(ℓ : GaloisRep.ratLocalizedAt ℓ)} := by
  haveI hprime : (Ideal.span {(ℓ : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hℓ.ne_zero)).mpr (Nat.prime_iff_prime_int.mp hℓ)
  haveI : IsLocalization.AtPrime (GaloisRep.ratLocalizedAt ℓ) (Ideal.span {(ℓ : ℤ)}) :=
    GaloisRep.isLocalization_ratLocalizedAt hℓ
  rw [← IsLocalization.AtPrime.map_eq_maximalIdeal (Ideal.span {(ℓ : ℤ)}) (GaloisRep.ratLocalizedAt ℓ),
    Ideal.map_span, Set.image_singleton, map_natCast]
