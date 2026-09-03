import Mathlib
import Definitions.Def_GaloisRep_CompletionBridge
import Theorems.Thm_exists_finiteDimensional_comap_localGaloisToGlobal_iff
import P2M.Util
namespace P2MW.S_IntermediateField_exists_finiteDimensional_localGaloisToGlobal_fixingSubgroupEquiv_symm_le

set_option autoImplicit false
set_option maxHeartbeats 1600000
open CategoryTheory

open IntermediateField in
theorem solution
    (q : ℕ) [Fact q.Prime]
    (K : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K]
    (E : IntermediateField K (PadicAlgCl q)) [FiniteDimensional K E] :
    ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ σ : PadicAlgCl q ≃ₐ[K] PadicAlgCl q,
        ((localGaloisToGlobal q).comp
        (K.fixingSubgroup.subtype.comp (IntermediateField.fixingSubgroupEquiv K).symm.toMonoidHom)) σ ∈ F.fixingSubgroup → σ ∈ E.fixingSubgroup := by
  classical
  let Ω := PadicAlgCl q
  let ι : (Ω ≃ₐ[K] Ω) →* (Ω ≃ₐ[ℚ_[q]] Ω) :=
    K.fixingSubgroup.subtype.comp (IntermediateField.fixingSubgroupEquiv K).symm.toMonoidHom
  have hι : ∀ (σ : Ω ≃ₐ[K] Ω) (x : Ω), ι σ x = σ x := fun _ _ => rfl

  let E' : IntermediateField ℚ_[q] Ω := E.restrictScalars ℚ_[q]
  haveI : FiniteDimensional ℚ_[q] E := FiniteDimensional.trans ℚ_[q] K E
  haveI : FiniteDimensional ℚ_[q] E' := ‹FiniteDimensional ℚ_[q] E›
  have key := (exists_finiteDimensional_comap_localGaloisToGlobal_iff q
    (fun U => ∀ σ : Ω ≃ₐ[K] Ω, ι σ ∈ U → σ ∈ E.fixingSubgroup)
    (fun U V hVU hU σ hσ => hU σ (hVU hσ))).2
    ⟨E', inferInstance, fun σ hσ => by
      rw [IntermediateField.mem_fixingSubgroup_iff] at hσ ⊢
      intro x hx
      rw [← hι]
      exact hσ x ((IntermediateField.mem_restrictScalars ℚ_[q]).2 hx)⟩
  obtain ⟨F, hF, h⟩ := key
  exact ⟨F, hF, fun σ hσ => h σ hσ⟩
