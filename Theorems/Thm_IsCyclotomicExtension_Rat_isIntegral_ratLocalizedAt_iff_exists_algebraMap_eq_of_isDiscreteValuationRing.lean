import Mathlib
import Definitions.Def_GaloisRep_Flat
import P2M.Util
import P2M.Sol.S_IsCyclotomicExtension_Rat_isIntegral_ratLocalizedAt_iff_exists_algebraMap_eq_of_isDiscreteValuationRing

set_option autoImplicit false

theorem IsCyclotomicExtension.Rat.isIntegral_ratLocalizedAt_iff_exists_algebraMap_eq_of_isDiscreteValuationRing
    (p : ℕ) [Fact p.Prime] (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (y : L) :
    IsIntegral ↥(GaloisRep.ratLocalizedAt p) y ↔ ∃ a : A, algebraMap A L a = y := by p2m_exact_reverting @_root_.P2MW.S_IsCyclotomicExtension_Rat_isIntegral_ratLocalizedAt_iff_exists_algebraMap_eq_of_isDiscreteValuationRing.solution
