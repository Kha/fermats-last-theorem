import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_ExtCitation_KummerBridge
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_LevelSubgroup
import Definitions.Def_NumberField_SUnitsMax
import Definitions.Def_NumberField_LevelArithmeticModP
import P2M.Util
import P2M.Sol.S_NumberField_LevelArith_d_eq_zero_and_d_eq_pow_smul_of_level_presentation_sUnitsMaxRep

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory groupCohomology ExtCitation NumberField IsDedekindDomain NumberField.LevelArith
open scoped NumberField.LevelArith

theorem NumberField.LevelArith.d_eq_zero_and_d_eq_pow_smul_of_level_presentation_sUnitsMaxRep
    {p : ℕ} (S : Finset Nat.Primes) (L F : IntermediateField ℚ (AlgebraicClosure ℚ)) [Normal ℚ ↥F]
    (u : (Fin 3 → ↥L.fixingSubgroup) → sUnitsMaxRep S L) (w₀ : (Fin 2 → ↥L.fixingSubgroup) → sUnitsMaxRep S L)
    (f : (Fin 3 → (↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype)) → ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype))) (b₀ : (Fin 2 → (↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype)) → ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype)))
    (hu : ∀ g : Fin 3 → ↥L.fixingSubgroup, u g = ((f (fun i => (g i : (↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype))) : ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype))) : sUnitsMaxRep S L))
    (hw : ∀ g : Fin 2 → ↥L.fixingSubgroup, w₀ g = ((b₀ (fun i => (g i : (↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype))) : ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype))) : sUnitsMaxRep S L))
    (k : ℕ) :
    ((((inhomogeneousCochains (sUnitsMaxRep S L)).d 3 4).hom u = 0) → ((inhomogeneousCochains ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype))).d 3 4).hom f = 0) ∧
    ((((inhomogeneousCochains (sUnitsMaxRep S L)).d 2 3).hom w₀ = (p ^ k : ℤ) • u) →
      ((inhomogeneousCochains ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype))).d 2 3).hom b₀ = (p ^ k : ℤ) • f) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_LevelArith_d_eq_zero_and_d_eq_pow_smul_of_level_presentation_sUnitsMaxRep.solution
