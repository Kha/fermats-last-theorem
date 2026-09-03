import Mathlib
import P2M.Util
import P2M.Sol.S_ModularCurve_FullLevel_AuxLevel_exists_subDVR_isFractionRing_adjoin_of_isPrimitiveRoot

set_option autoImplicit false

theorem ModularCurve.FullLevel.AuxLevel.exists_subDVR_isFractionRing_adjoin_of_isPrimitiveRoot
    (q : ℕ) [Fact q.Prime] (ℓ : ℕ) [Fact ℓ.Prime] (hℓq : ℓ ≠ q)
    (L : Type) [Field L] [CharZero L]
    (ξ : L) (hξ : IsPrimitiveRoot ξ (q * ℓ))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAq : (q : A) ∈ IsLocalRing.maximalIdeal A) :
    ∃ (A' : Type) (_ : CommRing A') (_ : IsDomain A') (_ : IsDiscreteValuationRing A')
      (_ : Algebra A' A) (_ : Algebra A' L) (_ : IsScalarTower A' A L)
      (_ : Algebra A' ↥(IntermediateField.adjoin ℚ ({ξ} : Set L)))
      (_ : IsScalarTower A' ↥(IntermediateField.adjoin ℚ ({ξ} : Set L)) L)
      (_ : IsFractionRing A' ↥(IntermediateField.adjoin ℚ ({ξ} : Set L))),
      Function.Injective (algebraMap A' A) ∧
      (IsLocalRing.maximalIdeal A).comap (algebraMap A' A) = IsLocalRing.maximalIdeal A' ∧
      ((q : A') ∈ IsLocalRing.maximalIdeal A') ∧
      Finite (IsLocalRing.ResidueField A') ∧
      (∃ ϖ ε : A', IsLocalRing.maximalIdeal A' = Ideal.span {ϖ} ∧ IsUnit ε ∧ ϖ ^ (q - 1) = ε * (q : A')) ∧
      (∃ r : A', algebraMap A' L r = ξ) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_FullLevel_AuxLevel_exists_subDVR_isFractionRing_adjoin_of_isPrimitiveRoot.solution
