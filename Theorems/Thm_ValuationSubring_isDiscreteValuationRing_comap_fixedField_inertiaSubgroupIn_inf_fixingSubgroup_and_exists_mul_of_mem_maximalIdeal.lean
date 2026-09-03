import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_ValuationSubring_isDiscreteValuationRing_comap_fixedField_inertiaSubgroupIn_inf_fixingSubgroup_and_exists_mul_of_mem_maximalIdeal
attribute [-instance] AlgebraicClosure.Rat.isGalois

set_option autoImplicit false

open IsLocalRing

theorem ValuationSubring.isDiscreteValuationRing_comap_fixedField_inertiaSubgroupIn_inf_fixingSubgroup_and_exists_mul_of_mem_maximalIdeal
    (p : ℕ) [Fact p.Prime]
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A)
    [Algebra A (AlgebraicClosure ℚ)] [Algebra L (AlgebraicClosure ℚ)] [IsScalarTower A L (AlgebraicClosure ℚ)]
    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    (hAPl : ∀ a : A, algebraMap A (AlgebraicClosure ℚ) a ∈ Pl) :
    IsDiscreteValuationRing ↥(Pl.comap (algebraMap ↥(IntermediateField.fixedField (Pl.inertiaSubgroupIn ℚ ⊓ (IsScalarTower.toAlgHom ℚ L (AlgebraicClosure ℚ)).fieldRange.fixingSubgroup)) (AlgebraicClosure ℚ))) ∧
    (∀ a : A, a ∈ IsLocalRing.maximalIdeal A → algebraMap A (AlgebraicClosure ℚ) a ∈ Pl.nonunits) ∧
    (∀ o : ↥(Pl.comap (algebraMap ↥(IntermediateField.fixedField (Pl.inertiaSubgroupIn ℚ ⊓ (IsScalarTower.toAlgHom ℚ L (AlgebraicClosure ℚ)).fieldRange.fixingSubgroup)) (AlgebraicClosure ℚ))), o ∈ IsLocalRing.maximalIdeal ↥(Pl.comap (algebraMap ↥(IntermediateField.fixedField (Pl.inertiaSubgroupIn ℚ ⊓ (IsScalarTower.toAlgHom ℚ L (AlgebraicClosure ℚ)).fieldRange.fixingSubgroup)) (AlgebraicClosure ℚ))) →
      ∃ (a : A) (o' : ↥(Pl.comap (algebraMap ↥(IntermediateField.fixedField (Pl.inertiaSubgroupIn ℚ ⊓ (IsScalarTower.toAlgHom ℚ L (AlgebraicClosure ℚ)).fieldRange.fixingSubgroup)) (AlgebraicClosure ℚ)))), a ∈ IsLocalRing.maximalIdeal A ∧
        ((o : ↥(IntermediateField.fixedField (Pl.inertiaSubgroupIn ℚ ⊓ (IsScalarTower.toAlgHom ℚ L (AlgebraicClosure ℚ)).fieldRange.fixingSubgroup))) : AlgebraicClosure ℚ) = algebraMap A (AlgebraicClosure ℚ) a * ((o' : ↥(IntermediateField.fixedField (Pl.inertiaSubgroupIn ℚ ⊓ (IsScalarTower.toAlgHom ℚ L (AlgebraicClosure ℚ)).fieldRange.fixingSubgroup))) : AlgebraicClosure ℚ)) := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_isDiscreteValuationRing_comap_fixedField_inertiaSubgroupIn_inf_fixingSubgroup_and_exists_mul_of_mem_maximalIdeal.solution
