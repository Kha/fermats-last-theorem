import Mathlib
import Definitions.Def_GaloisRep_CompletionBridge
import Definitions.Def_GaloisRep_ComplexConjugation
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_NumberField_ArchimedeanIdeleModule
import Definitions.Def_GroupCohomology_GaloisUnitsInflation
import Definitions.Def_GroupCohomology_ContinuousH1
import P2M.Util
import P2M.Sol.S_NumberField_PlaceDecomp_exists_forall_mem_asIdeal_iff_norm_padicEmbedding_lt_one
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory NumberField IsDedekindDomain ExtCitation
open scoped NumberField.PlaceDecomp NumberField.InfPlaceDecomp

theorem NumberField.PlaceDecomp.exists_forall_mem_asIdeal_iff_norm_padicEmbedding_lt_one
    (q : ℕ) [Fact q.Prime]
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F] [IsGalois ℚ ↥F]
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    ∃ w : HeightOneSpectrum (𝓞 ↥F),
      (∀ x : 𝓞 ↥F, x ∈ w.asIdeal ↔ ‖padicEmbedding q (σ ((x : ↥F) : AlgebraicClosure ℚ))‖ < 1) ∧ ((q : ℕ) : 𝓞 ↥F) ∈ w.asIdeal := by p2m_exact_reverting @_root_.P2MW.S_NumberField_PlaceDecomp_exists_forall_mem_asIdeal_iff_norm_padicEmbedding_lt_one.solution
