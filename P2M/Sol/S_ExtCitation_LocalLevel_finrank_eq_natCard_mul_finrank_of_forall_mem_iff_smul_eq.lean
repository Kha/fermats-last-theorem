import Mathlib
import Definitions.Def_ExtCitation_LocalLevelResidues
import Definitions.Def_GroupCohomology_CyclicCarry
import P2M.Util
namespace P2MW.S_ExtCitation_LocalLevel_finrank_eq_natCard_mul_finrank_of_forall_mem_iff_smul_eq

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
p2m_open "CategoryTheory groupCohomology ExtCitation.LocalLevel P2MW.S_ExtCitation_LocalLevel_finrank_eq_natCard_mul_finrank_of_forall_mem_iff_smul_eq.ExtCitation.LocalLevel"

namespace ExtCitation
namespace LocalLevel
namespace Ws25GC
p2m_open "ExtCitation.LocalLevel ExtCitation"

variable {q : ℕ} [Fact q.Prime]
variable {L : IntermediateField ℚ_[q] (PadicAlgCl q)}
variable {G : Type} [Group G] [MulSemiringAction G L]

theorem smulCommClass (hG : ∀ (g : G) (x : ℚ_[q]), g • algebraMap ℚ_[q] L x = algebraMap ℚ_[q] L x) :
    SMulCommClass G ℚ_[q] L :=
  ⟨fun g c x => by rw [Algebra.smul_def, Algebra.smul_def, smul_mul', hG g c]⟩

end ExtCitation.LocalLevel.Ws25GC

open ExtCitation.LocalLevel.Ws25GC in
theorem solution (q : ℕ) [Fact q.Prime]
    (L : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] L]
    (G : Type) [Group G] [Finite G] [MulSemiringAction G L] [FaithfulSMul G L]
    (hG : ∀ (g : G) (x : ℚ_[q]), g • algebraMap ℚ_[q] L x = algebraMap ℚ_[q] L x)
    (K : IntermediateField ℚ_[q] (PadicAlgCl q)) (hKL : K ≤ L)
    (hK : ∀ x : L, (x : PadicAlgCl q) ∈ K ↔ ∀ g : G, g • x = x) :
    Module.finrank ℚ_[q] L = Nat.card G * Module.finrank ℚ_[q] K := by
  classical
  letI := smulCommClass hG
  letI : Fintype G := Fintype.ofFinite G

  obtain ⟨E, hE⟩ : ∃ E : IntermediateField ℚ_[q] L, E = FixedPoints.intermediateField (F := ℚ_[q]) (E := L) G := ⟨_, rfl⟩
  have hmemE : ∀ x : L, x ∈ E ↔ ∀ g : G, g • x = x := fun x => by rw [hE]; exact Iff.rfl
  have hArtin : Module.finrank E L = Fintype.card G := by
    subst hE
    exact FixedPoints.finrank_eq_card G L

  have hKE : Module.finrank ℚ_[q] K = Module.finrank ℚ_[q] E := by
    obtain ⟨φ, hφ⟩ : ∃ φ : K →ₗ[ℚ_[q]] E, ∀ x : K, ((φ x : L) : PadicAlgCl q) = (x : PadicAlgCl q) :=
      ⟨{ toFun := fun x => ⟨⟨(x : PadicAlgCl q), hKL x.2⟩, (hmemE _).mpr ((hK ⟨(x : PadicAlgCl q), hKL x.2⟩).mp x.2)⟩
         map_add' := fun x y => Subtype.ext (Subtype.ext rfl)
         map_smul' := fun c x => Subtype.ext (Subtype.ext (by
           simp only [RingHom.id_apply]
           rw [IntermediateField.coe_smul, IntermediateField.coe_smul]
           rfl)) },
       fun _ => rfl⟩
    have hinj : Function.Injective φ := by
      intro x y hxy
      apply Subtype.ext
      rw [← hφ x, ← hφ y, hxy]
    have hsurj : Function.Surjective φ := by
      intro y
      have hy : ((y : L) : PadicAlgCl q) ∈ K := (hK (y : L)).mpr ((hmemE _).mp y.2)
      refine ⟨⟨((y : L) : PadicAlgCl q), hy⟩, ?_⟩
      apply Subtype.ext; apply Subtype.ext
      exact hφ _
    exact (LinearEquiv.ofBijective φ ⟨hinj, hsurj⟩).finrank_eq
  rw [hKE, ← Module.finrank_mul_finrank ℚ_[q] E L, hArtin, Nat.card_eq_fintype_card, mul_comm]
