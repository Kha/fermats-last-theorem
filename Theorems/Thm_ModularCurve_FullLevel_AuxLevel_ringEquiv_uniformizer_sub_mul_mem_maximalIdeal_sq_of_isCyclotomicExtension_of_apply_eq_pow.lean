import Mathlib
import P2M.Util
import P2M.Sol.S_ModularCurve_FullLevel_AuxLevel_ringEquiv_uniformizer_sub_mul_mem_maximalIdeal_sq_of_isCyclotomicExtension_of_apply_eq_pow

set_option autoImplicit false

theorem ModularCurve.FullLevel.AuxLevel.ringEquiv_uniformizer_sub_mul_mem_maximalIdeal_sq_of_isCyclotomicExtension_of_apply_eq_pow
    (q : ℕ) [Fact q.Prime] (ℓ : ℕ) [Fact ℓ.Prime] (hℓq : ℓ ≠ q)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {q * ℓ} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ q)
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAq : (q : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ x : A, algebraMap A L x = ζ)
    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ})
    (d : (ZMod q)ˣ) (σL : L ≃+* L) (σA : A ≃+* A)
    (hσ : ∀ a : A, algebraMap A L (σA a) = σL (algebraMap A L a))
    (hinert : ∀ a : A, σA a - a ∈ IsLocalRing.maximalIdeal A)
    (hd : σL ζ = ζ ^ ((d : ZMod q).val)) :
    σA ϖ - (((d : ZMod q).val : ℕ) : A) * ϖ ∈ (IsLocalRing.maximalIdeal A) ^ 2 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_FullLevel_AuxLevel_ringEquiv_uniformizer_sub_mul_mem_maximalIdeal_sq_of_isCyclotomicExtension_of_apply_eq_pow.solution
