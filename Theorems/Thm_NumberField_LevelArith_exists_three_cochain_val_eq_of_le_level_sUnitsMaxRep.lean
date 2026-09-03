import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_ExtCitation_KummerBridge
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_LevelSubgroup
import Definitions.Def_NumberField_SUnitsMax
import Definitions.Def_NumberField_LevelArithmeticModP
import P2M.Util
import P2M.Sol.S_NumberField_LevelArith_exists_three_cochain_val_eq_of_le_level_sUnitsMaxRep

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory groupCohomology ExtCitation NumberField IsDedekindDomain NumberField.LevelArith
open scoped NumberField.LevelArith

theorem NumberField.LevelArith.exists_three_cochain_val_eq_of_le_level_sUnitsMaxRep
    {p : ℕ} (S : Finset Nat.Primes) (L F F₁ : IntermediateField ℚ (AlgebraicClosure ℚ)) (hFF₁ : F ≤ F₁)
    [FiniteDimensional ℚ ↥F] [Normal ℚ ↥F] [FiniteDimensional ℚ ↥F₁] [Normal ℚ ↥F₁]
    (f : ((Fin 3 → (↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype)) → ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype))))
    (k : ℕ) (b₀ : ((Fin 2 → (↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype)) → ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype))))
    (hk : ((inhomogeneousCochains ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype))).d 2 3).hom b₀ = (p ^ k : ℤ) • f) :
    ∃ (f₁ : ((Fin 3 → (↥L.fixingSubgroup ⧸ F₁.fixingSubgroup.comap L.fixingSubgroup.subtype)) → ((sUnitsMaxRep S L).quotientToInvariants (F₁.fixingSubgroup.comap L.fixingSubgroup.subtype)))) (b₀₁ : ((Fin 2 → (↥L.fixingSubgroup ⧸ F₁.fixingSubgroup.comap L.fixingSubgroup.subtype)) → ((sUnitsMaxRep S L).quotientToInvariants (F₁.fixingSubgroup.comap L.fixingSubgroup.subtype)))),
      (((inhomogeneousCochains ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype))).d 3 4).hom f = 0 → ((inhomogeneousCochains ((sUnitsMaxRep S L).quotientToInvariants (F₁.fixingSubgroup.comap L.fixingSubgroup.subtype))).d 3 4).hom f₁ = 0) ∧
      ((inhomogeneousCochains ((sUnitsMaxRep S L).quotientToInvariants (F₁.fixingSubgroup.comap L.fixingSubgroup.subtype))).d 2 3).hom b₀₁ = (p ^ k : ℤ) • f₁ ∧
      (∀ g : Fin 3 → ↥L.fixingSubgroup,
        ((f₁ (fun i => (g i : (↥L.fixingSubgroup ⧸ F₁.fixingSubgroup.comap L.fixingSubgroup.subtype))) : ((sUnitsMaxRep S L).quotientToInvariants (F₁.fixingSubgroup.comap L.fixingSubgroup.subtype))) : sUnitsMaxRep S L)
          = ((f (fun i => (g i : (↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype))) : ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype))) : sUnitsMaxRep S L)) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_LevelArith_exists_three_cochain_val_eq_of_le_level_sUnitsMaxRep.solution
