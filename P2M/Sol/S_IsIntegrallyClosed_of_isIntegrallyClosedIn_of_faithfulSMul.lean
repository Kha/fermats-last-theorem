import Mathlib
import P2M.Util
namespace P2MW.S_IsIntegrallyClosed_of_isIntegrallyClosedIn_of_faithfulSMul

theorem solution
    (A F : Type*) [CommRing A] [IsDomain A] [Field F] [Algebra A F] [FaithfulSMul A F]
    [IsIntegrallyClosedIn A F] : IsIntegrallyClosed A := by
  rw [isIntegrallyClosed_iff (FractionRing A)]
  intro x hx
  have hinj : Function.Injective (algebraMap A F) := FaithfulSMul.algebraMap_injective A F
  let φ : FractionRing A →ₐ[A] F :=
    { IsFractionRing.lift hinj with
      commutes' := fun a => by simp [IsFractionRing.lift_algebraMap] }
  have hφ : ∀ y, φ y = IsFractionRing.lift hinj y := fun _ => rfl
  have hx' : IsIntegral A (φ x) := hx.map φ
  obtain ⟨a, ha⟩ := IsIntegrallyClosedIn.algebraMap_eq_of_integral hx'
  refine ⟨a, ?_⟩
  apply (IsFractionRing.lift hinj : FractionRing A →+* F).injective
  rw [IsFractionRing.lift_algebraMap, ← hφ]
  exact ha
