import Mathlib
import Definitions.Def_GroupCohomology_LevelSubgroup
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevelInflation
import Definitions.Def_GroupCohomology_ContinuousH2Inflation
import Definitions.Def_NumberField_SUnitsMax
import Definitions.Def_NumberField_LevelArithmeticModP
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_NumberField_PlaceAbove
import Definitions.Def_ExtCitation_LocalLevel_FundamentalClass
import Definitions.Def_NumberField_SIdeleModule
import Definitions.Def_NumberField_ArchimedeanIdeleModule
import P2M.Util
import P2M.Sol.S_NumberField_LevelArith_exists_two_cochain_quotientToInvariants_sUnitsMaxRep_eq_d_of_transport

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory groupCohomology ExtCitation NumberField IsDedekindDomain M4aHerbrand NumberField.LevelArith
open scoped NumberField.LevelArith NumberField.PlaceDecomp
open scoped NumberField.InfPlaceDecomp

theorem NumberField.LevelArith.exists_two_cochain_quotientToInvariants_sUnitsMaxRep_eq_d_of_transport
    (S : Finset Nat.Primes) (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ ↥L]
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ ↥F] [Normal ℚ ↥F]
    (F₂ : IntermediateField ℚ (AlgebraicClosure ℚ)) (hLF₂ : L ≤ F₂) [FiniteDimensional ℚ ↥F₂] [Normal ℚ ↥F₂] [IsGalois ↥L ↥(levelField L F₂ hLF₂)]
    (ι₂ : (↥(levelField L F₂ hLF₂) ≃ₐ[↥L] ↥(levelField L F₂ hLF₂)) →* (↥L.fixingSubgroup ⧸ F₂.fixingSubgroup.comap L.fixingSubgroup.subtype))
    (hι₂ : ∀ g : ↥L.fixingSubgroup, ι₂ (levelGal L F₂ hLF₂ g) = (g : (↥L.fixingSubgroup ⧸ F₂.fixingSubgroup.comap L.fixingSubgroup.subtype)))
    (φ₂ : Rep.res ι₂ ((sUnitsMaxRep S L).quotientToInvariants (F₂.fixingSubgroup.comap L.fixingSubgroup.subtype)) ⟶ (NumberField.SUnits.sUnitsRep ↥L ↥(levelField L F₂ hLF₂) (placesOverPrimesFinset ↥L S)))
    (hφ₂ : Function.Bijective φ₂.hom)
    (hφval₂ : ∀ x, ((NumberField.SUnits.val ↥L ↥(levelField L F₂ hLF₂) (placesOverPrimesFinset ↥L S) (φ₂.hom x) : ↥(levelField L F₂ hLF₂)) : AlgebraicClosure ℚ)
        = ((sUnitsMaxRep.val S L (x.1 : sUnitsMaxRep S L) : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ))
    (f : ((Fin 3 → (↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype)) → ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype))))
    (e₂ : (Fin 2 → (↥(levelField L F₂ hLF₂) ≃ₐ[↥L] ↥(levelField L F₂ hLF₂))) → (NumberField.SUnits.sUnitsRep ↥L ↥(levelField L F₂ hLF₂) (placesOverPrimesFinset ↥L S)))
    (hfe₂ : ∀ g : Fin 3 → ↥L.fixingSubgroup,
        ((NumberField.SUnits.val ↥L ↥(levelField L F₂ hLF₂) (placesOverPrimesFinset ↥L S) (((inhomogeneousCochains (NumberField.SUnits.sUnitsRep ↥L ↥(levelField L F₂ hLF₂) (placesOverPrimesFinset ↥L S))).d 2 3).hom e₂ (fun i => levelGal L F₂ hLF₂ (g i))) : ↥(levelField L F₂ hLF₂)) : AlgebraicClosure ℚ)
          = ((sUnitsMaxRep.val S L ((f (fun i => (g i : (↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype))) : ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype))) : sUnitsMaxRep S L) : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ)) :
    ∃ b : ((Fin 2 → (↥L.fixingSubgroup ⧸ F₂.fixingSubgroup.comap L.fixingSubgroup.subtype)) → ((sUnitsMaxRep S L).quotientToInvariants (F₂.fixingSubgroup.comap L.fixingSubgroup.subtype))),
      ∀ g : Fin 3 → ↥L.fixingSubgroup,
        ((f (fun i => (g i : (↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype))) : ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype))) : sUnitsMaxRep S L)
          = ((((inhomogeneousCochains ((sUnitsMaxRep S L).quotientToInvariants (F₂.fixingSubgroup.comap L.fixingSubgroup.subtype))).d 2 3).hom b (fun i => (g i : (↥L.fixingSubgroup ⧸ F₂.fixingSubgroup.comap L.fixingSubgroup.subtype))) : ((sUnitsMaxRep S L).quotientToInvariants (F₂.fixingSubgroup.comap L.fixingSubgroup.subtype))) : sUnitsMaxRep S L) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_LevelArith_exists_two_cochain_quotientToInvariants_sUnitsMaxRep_eq_d_of_transport.solution
