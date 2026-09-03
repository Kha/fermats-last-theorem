import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_ValuationSubring_exists_ringHom_comap_fixedField_inertiaSubgroupIn_inf_fixingSubgroup_comp_eq_and_isDiscreteValuationRing_and_map_maximalIdeal_eq
attribute [-instance] AlgebraicClosure.Rat.isGalois

set_option autoImplicit false

open IsLocalRing

theorem ValuationSubring.exists_ringHom_comap_fixedField_inertiaSubgroupIn_inf_fixingSubgroup_comp_eq_and_isDiscreteValuationRing_and_map_maximalIdeal_eq
    (p : ℕ) [Fact p.Prime]
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A)
    [Algebra A (AlgebraicClosure ℚ)] [Algebra L (AlgebraicClosure ℚ)] [IsScalarTower A L (AlgebraicClosure ℚ)]
    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    (ρ : A →+* ↥Pl) (hρ : Pl.subtype.comp ρ = algebraMap A (AlgebraicClosure ℚ)) :
    ∃ (ι : ↥(Pl.comap (algebraMap ↥(IntermediateField.fixedField (Pl.inertiaSubgroupIn ℚ ⊓ (IsScalarTower.toAlgHom ℚ L (AlgebraicClosure ℚ)).fieldRange.fixingSubgroup)) (AlgebraicClosure ℚ))) →+* ↥Pl)
      (ρO : A →+* ↥(Pl.comap (algebraMap ↥(IntermediateField.fixedField (Pl.inertiaSubgroupIn ℚ ⊓ (IsScalarTower.toAlgHom ℚ L (AlgebraicClosure ℚ)).fieldRange.fixingSubgroup)) (AlgebraicClosure ℚ)))),
      (∀ o : ↥(Pl.comap (algebraMap ↥(IntermediateField.fixedField (Pl.inertiaSubgroupIn ℚ ⊓ (IsScalarTower.toAlgHom ℚ L (AlgebraicClosure ℚ)).fieldRange.fixingSubgroup)) (AlgebraicClosure ℚ))),
        ((ι o : ↥Pl) : AlgebraicClosure ℚ) = algebraMap ↥(IntermediateField.fixedField (Pl.inertiaSubgroupIn ℚ ⊓ (IsScalarTower.toAlgHom ℚ L (AlgebraicClosure ℚ)).fieldRange.fixingSubgroup)) (AlgebraicClosure ℚ) (o : ↥(IntermediateField.fixedField (Pl.inertiaSubgroupIn ℚ ⊓ (IsScalarTower.toAlgHom ℚ L (AlgebraicClosure ℚ)).fieldRange.fixingSubgroup)))) ∧
      ι.comp ρO = ρ ∧
      Function.Injective ι ∧
      IsDiscreteValuationRing ↥(Pl.comap (algebraMap ↥(IntermediateField.fixedField (Pl.inertiaSubgroupIn ℚ ⊓ (IsScalarTower.toAlgHom ℚ L (AlgebraicClosure ℚ)).fieldRange.fixingSubgroup)) (AlgebraicClosure ℚ))) ∧
      Ideal.map ρO (IsLocalRing.maximalIdeal A) = IsLocalRing.maximalIdeal ↥(Pl.comap (algebraMap ↥(IntermediateField.fixedField (Pl.inertiaSubgroupIn ℚ ⊓ (IsScalarTower.toAlgHom ℚ L (AlgebraicClosure ℚ)).fieldRange.fixingSubgroup)) (AlgebraicClosure ℚ))) ∧
      (∀ o : ↥(Pl.comap (algebraMap ↥(IntermediateField.fixedField (Pl.inertiaSubgroupIn ℚ ⊓ (IsScalarTower.toAlgHom ℚ L (AlgebraicClosure ℚ)).fieldRange.fixingSubgroup)) (AlgebraicClosure ℚ))), ι o ∈ IsLocalRing.maximalIdeal ↥Pl ↔ o ∈ IsLocalRing.maximalIdeal ↥(Pl.comap (algebraMap ↥(IntermediateField.fixedField (Pl.inertiaSubgroupIn ℚ ⊓ (IsScalarTower.toAlgHom ℚ L (AlgebraicClosure ℚ)).fieldRange.fixingSubgroup)) (AlgebraicClosure ℚ)))) ∧
      Function.Surjective (fun o : ↥(Pl.comap (algebraMap ↥(IntermediateField.fixedField (Pl.inertiaSubgroupIn ℚ ⊓ (IsScalarTower.toAlgHom ℚ L (AlgebraicClosure ℚ)).fieldRange.fixingSubgroup)) (AlgebraicClosure ℚ))) => IsLocalRing.residue ↥Pl (ι o)) ∧
      (∀ σ ∈ Pl.inertiaSubgroupIn ℚ ⊓ (IsScalarTower.toAlgHom ℚ L (AlgebraicClosure ℚ)).fieldRange.fixingSubgroup,
        ∀ o : ↥(Pl.comap (algebraMap ↥(IntermediateField.fixedField (Pl.inertiaSubgroupIn ℚ ⊓ (IsScalarTower.toAlgHom ℚ L (AlgebraicClosure ℚ)).fieldRange.fixingSubgroup)) (AlgebraicClosure ℚ))), σ ((ι o : ↥Pl) : AlgebraicClosure ℚ) = ((ι o : ↥Pl) : AlgebraicClosure ℚ)) := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_exists_ringHom_comap_fixedField_inertiaSubgroupIn_inf_fixingSubgroup_comp_eq_and_isDiscreteValuationRing_and_map_maximalIdeal_eq.solution
