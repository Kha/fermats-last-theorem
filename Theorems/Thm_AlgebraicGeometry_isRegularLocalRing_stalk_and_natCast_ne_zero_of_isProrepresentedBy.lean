import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_isRegularLocalRing_stalk_and_natCast_ne_zero_of_isProrepresentedBy

set_option autoImplicit false

p2m_open "CategoryTheory AlgebraicGeometry~finite_residueField_stalk_of_isClosed_of_locallyOfFiniteType"

theorem AlgebraicGeometry.isRegularLocalRing_stalk_and_natCast_ne_zero_of_isProrepresentedBy
    {q : ℕ} [Fact q.Prime]
    {Y : Scheme.{0}} (πY : Y ⟶ Spec (CommRingCat.of ℤ_[q])) [LocallyOfFiniteType πY]
    (y : Y) (hy : IsClosed ({y} : Set Y)) (hyq : πY y = IsLocalRing.closedPoint ℤ_[q])
    (Onr : Type) [CommRing Onr] [IsDomain Onr] [IsDiscreteValuationRing Onr] [CharZero Onr] [Algebra ℤ_[q] Onr]
    (hOnr_max : (Ideal.span {algebraMap ℤ_[q] Onr (q : ℤ_[q])}).IsMaximal)
    (xbar : Y.presheaf.stalk y →+* IsLocalRing.ResidueField Onr)
    (hxbar : RingHom.ker xbar = IsLocalRing.maximalIdeal (Y.presheaf.stalk y))
    (R : Type) [CommRing R] [IsRegularLocalRing R] [Algebra Onr R] [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    (resR : R →+* IsLocalRing.ResidueField Onr) (hresR : resR.comp (algebraMap Onr R) = IsLocalRing.residue Onr)
    (φ : Y.presheaf.stalk y →+* R) (hφ : resR.comp φ = xbar)
    (huniv :
      (∀ (A : Type) [CommRing A] [IsLocalRing A] [IsArtinianRing A] [Algebra Onr A]
          (resA : A →+* IsLocalRing.ResidueField Onr), Function.Surjective resA →
          resA.comp (algebraMap Onr A) = IsLocalRing.residue Onr →
        ∀ ψ : Y.presheaf.stalk y →+* A, resA.comp ψ = xbar →
          ∃! χ : R →ₐ[Onr] A, resA.comp χ.toRingHom = resR ∧ χ.toRingHom.comp φ = ψ))
    (hqR : ((q : ℕ) : R) ≠ 0) :
    IsRegularLocalRing (Y.presheaf.stalk y) ∧ ((q : ℕ) : Y.presheaf.stalk y) ≠ 0 := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_isRegularLocalRing_stalk_and_natCast_ne_zero_of_isProrepresentedBy.solution
