import Mathlib
import P2M.Util
import P2M.Sol.S_ModularCurve_XOneP_algebraMap_smul_eq_of_isCyclotomicExtension_of_charP

set_option autoImplicit false

theorem ModularCurve.XOneP.algebraMap_smul_eq_of_isCyclotomicExtension_of_charP
    (p : ℕ) [Fact p.Prime]
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    (k : Type) [Field k] [CharP k p] [Algebra A k]
    [MulSemiringAction (L ≃ₐ[ℚ] L) A]
    (hΓA : ∀ (s : L ≃ₐ[ℚ] L) (a : A), algebraMap A L (s • a) = s (algebraMap A L a)) :
    ∀ (s : L ≃ₐ[ℚ] L) (a : A), algebraMap A k (s • a) = algebraMap A k a := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_XOneP_algebraMap_smul_eq_of_isCyclotomicExtension_of_charP.solution
