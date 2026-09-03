import Mathlib
import P2M.Util
import P2M.Sol.S_IsCyclotomicExtension_exists_mulSemiringAction_algebraMap_smul_eq_of_isDiscreteValuationRing_of_mem_maximalIdeal

set_option autoImplicit false

theorem IsCyclotomicExtension.exists_mulSemiringAction_algebraMap_smul_eq_of_isDiscreteValuationRing_of_mem_maximalIdeal
    (p : ℕ) [Fact p.Prime]
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ) :
    ∃ inst : MulSemiringAction (L ≃ₐ[ℚ] L) A,
      ∀ (s : L ≃ₐ[ℚ] L) (a : A), algebraMap A L (s • a) = s (algebraMap A L a) := by p2m_exact_reverting @_root_.P2MW.S_IsCyclotomicExtension_exists_mulSemiringAction_algebraMap_smul_eq_of_isDiscreteValuationRing_of_mem_maximalIdeal.solution
