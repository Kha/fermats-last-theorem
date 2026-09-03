import Mathlib
import Definitions.Def_ModularCurve_LaurentCoeff
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_ringEquiv_restrict_coeffMap_laurentBaseChange_of_normal

set_option autoImplicit false

open IsLocalRing

theorem ModularCurve.exists_ringEquiv_restrict_coeffMap_laurentBaseChange_of_normal
    (L₀ : Type) [Field L₀] [CharZero L₀] [Normal ℚ L₀]
    (L : Type) [Field L] [CharZero L] (i : L₀ →+* L)
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (A₀ : Type) [CommRing A₀] [IsDomain A₀] [IsDiscreteValuationRing A₀] [Algebra A₀ L₀] [IsFractionRing A₀ L₀]
    [Algebra A₀ A] [IsLocalHom (algebraMap A₀ A)] (hinj : Function.Injective (algebraMap A₀ A))
    (hA₀A : ∀ a : A₀, algebraMap A L (algebraMap A₀ A a) = i (algebraMap A₀ L₀ a))
    (F₀ : IntermediateField ℚ (LaurentSeries ℚ))
    (K₀ : IntermediateField L₀ (LaurentSeries L₀)) (hK₀ : K₀ = ModularCurve.laurentBaseChange L₀ F₀)
    (K : IntermediateField L (LaurentSeries L)) (hK : K = ModularCurve.laurentBaseChange L F₀)
    (cK : ↥K₀ →+* ↥K)
    (hcK : ∀ x : ↥K₀, ((cK x : ↥K) : LaurentSeries L) = ModularCurve.coeffMap i ((x : ↥K₀) : LaurentSeries L₀))
    (σL : L ≃+* L) (σA : A ≃+* A)
    (hσ : ∀ a : A, algebraMap A L (σA a) = σL (algebraMap A L a))
    (hσm : ∀ a : A, σA a - a ∈ maximalIdeal A)
    (τ : ↥K ≃+* ↥K)
    (hτ : ∀ x : ↥K, ((τ x : ↥K) : LaurentSeries L) = ModularCurve.coeffMap σL.toRingHom ((x : ↥K) : LaurentSeries L)) :
    ∃ (σL₀ : L₀ ≃+* L₀) (σA₀ : A₀ ≃+* A₀) (τ₀ : ↥K₀ ≃+* ↥K₀),
      (∀ x : L₀, i (σL₀ x) = σL (i x)) ∧
      (∀ a : A₀, algebraMap A₀ A (σA₀ a) = σA (algebraMap A₀ A a)) ∧
      (∀ a : A₀, algebraMap A₀ L₀ (σA₀ a) = σL₀ (algebraMap A₀ L₀ a)) ∧
      (∀ a : A₀, σA₀ a - a ∈ maximalIdeal A₀) ∧
      (∀ x : ↥K₀, ((τ₀ x : ↥K₀) : LaurentSeries L₀) =
        ModularCurve.coeffMap σL₀.toRingHom ((x : ↥K₀) : LaurentSeries L₀)) ∧
      (∀ x : ↥K₀, cK (τ₀ x) = τ (cK x)) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_ringEquiv_restrict_coeffMap_laurentBaseChange_of_normal.solution
