import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_GaloisRep_Flat
import P2M.Util
import P2M.Sol.S_ValuationSubring_exists_ringHom_comap_fixedField_inertiaSubgroupIn_comp_eq_and_isDiscreteValuationRing
attribute [-instance] AlgebraicClosure.Rat.isGalois

set_option autoImplicit false

open IsLocalRing

theorem ValuationSubring.exists_ringHom_comap_fixedField_inertiaSubgroupIn_comp_eq_and_isDiscreteValuationRing
    (p : ℕ) [Fact p.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (ρ : ↥(GaloisRep.ratLocalizedAt p) →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ)) :
    ∃ (ι : ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))) →+* ↥A)
      (ρO : ↥(GaloisRep.ratLocalizedAt p) →+* ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)))),
      (∀ o : ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))),
        ((ι o : ↥A) : AlgebraicClosure ℚ) =
          algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)
            (o : ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)))) ∧
      ι.comp ρO = ρ ∧
      Function.Injective ι ∧
      IsDiscreteValuationRing ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))) ∧
      IsLocalRing.maximalIdeal ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))) = Ideal.span {((p : ℕ) : ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))))} ∧
      (∀ o : ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))), ι o ∈ IsLocalRing.maximalIdeal ↥A ↔ o ∈ IsLocalRing.maximalIdeal ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)))) ∧
      Function.Surjective (fun o : ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))) => IsLocalRing.residue ↥A (ι o)) ∧
      (∀ τ : ↥(A.decompositionSubgroup ℚ), τ ∈ A.inertiaSubgroup ℚ → ∀ o : ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))), τ • (ι o) = ι o) := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_exists_ringHom_comap_fixedField_inertiaSubgroupIn_comp_eq_and_isDiscreteValuationRing.solution
