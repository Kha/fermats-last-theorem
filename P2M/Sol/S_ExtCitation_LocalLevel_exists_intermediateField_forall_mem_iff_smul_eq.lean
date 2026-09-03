import Mathlib
import Definitions.Def_ExtCitation_LocalLevelResidues
import Definitions.Def_GroupCohomology_CyclicCarry
import P2M.Util
namespace P2MW.S_ExtCitation_LocalLevel_exists_intermediateField_forall_mem_iff_smul_eq

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
p2m_open "CategoryTheory groupCohomology ExtCitation.LocalLevel P2MW.S_ExtCitation_LocalLevel_exists_intermediateField_forall_mem_iff_smul_eq.ExtCitation.LocalLevel"

namespace ExtCitation
namespace LocalLevel
namespace Ws25FB
p2m_open "ExtCitation.LocalLevel ExtCitation"

variable {q : ℕ} [Fact q.Prime]
variable {L : IntermediateField ℚ_[q] (PadicAlgCl q)}
variable {G : Type} [Group G] [MulSemiringAction G L]

theorem smulCommClass (hG : ∀ (g : G) (x : ℚ_[q]), g • algebraMap ℚ_[q] L x = algebraMap ℚ_[q] L x) :
    SMulCommClass G ℚ_[q] L :=
  ⟨fun g c x => by rw [Algebra.smul_def, Algebra.smul_def, smul_mul', hG g c]⟩

end ExtCitation.LocalLevel.Ws25FB

open ExtCitation.LocalLevel.Ws25FB in
theorem solution (q : ℕ) [Fact q.Prime]
    (L : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] L]
    (G : Type) [Group G] [Finite G] [MulSemiringAction G L] [FaithfulSMul G L]
    (hG : ∀ (g : G) (x : ℚ_[q]), g • algebraMap ℚ_[q] L x = algebraMap ℚ_[q] L x) :
    ∃ (K : IntermediateField ℚ_[q] (PadicAlgCl q)) (_ : FiniteDimensional ℚ_[q] K), K ≤ L ∧
      ∀ x : L, (x : PadicAlgCl q) ∈ K ↔ ∀ g : G, g • x = x := by
  letI := smulCommClass hG
  haveI : FiniteDimensional ℚ_[q] (FixedPoints.intermediateField (F := ℚ_[q]) (E := L) G) :=
    IntermediateField.finiteDimensional_left _
  refine ⟨IntermediateField.lift (FixedPoints.intermediateField (F := ℚ_[q]) (E := L) G),
    LinearEquiv.finiteDimensional
      (IntermediateField.liftAlgEquiv (FixedPoints.intermediateField (F := ℚ_[q]) (E := L) G)).toLinearEquiv,
    IntermediateField.lift_le _, fun x => ?_⟩
  rw [IntermediateField.mem_lift]
  exact Iff.rfl
