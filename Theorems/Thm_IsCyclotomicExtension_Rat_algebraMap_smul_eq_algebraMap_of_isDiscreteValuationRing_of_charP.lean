import Mathlib
import P2M.Util
import P2M.Sol.S_IsCyclotomicExtension_Rat_algebraMap_smul_eq_algebraMap_of_isDiscreteValuationRing_of_charP

set_option autoImplicit false

theorem IsCyclotomicExtension.Rat.algebraMap_smul_eq_algebraMap_of_isDiscreteValuationRing_of_charP
    (p : ℕ) [Fact p.Prime] (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A)
    (k : Type) [Field k] [CharP k p] [Algebra A k]
    [MulSemiringAction (L ≃ₐ[ℚ] L) A]
    (hΓA : ∀ (s : L ≃ₐ[ℚ] L) (a : A), algebraMap A L (s • a) = s (algebraMap A L a)) :
    ∀ (s : L ≃ₐ[ℚ] L) (a : A), algebraMap A k (s • a) = algebraMap A k a := by p2m_exact_reverting @_root_.P2MW.S_IsCyclotomicExtension_Rat_algebraMap_smul_eq_algebraMap_of_isDiscreteValuationRing_of_charP.solution
