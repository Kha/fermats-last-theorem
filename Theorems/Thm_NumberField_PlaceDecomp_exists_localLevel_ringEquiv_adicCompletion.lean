import Mathlib
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_ExtCitation_LocalLevelResidues
import P2M.Util
import P2M.Sol.S_NumberField_PlaceDecomp_exists_localLevel_ringEquiv_adicCompletion

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxSynthPendingDepth 3
open CategoryTheory groupCohomology ExtCitation.LocalLevel IsDedekindDomain NumberField
open scoped NumberField.PlaceDecomp

theorem NumberField.PlaceDecomp.exists_localLevel_ringEquiv_adicCompletion
    (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K] [IsGalois E K]
    (w : HeightOneSpectrum (𝓞 K)) :
    ∃ (q : ℕ) (_ : Fact q.Prime) (L' : IntermediateField ℚ_[q] (PadicAlgCl q)) (_ : FiniteDimensional ℚ_[q] L')
      (_ : MulSemiringAction (decomp E K w) L') (_ : FaithfulSMul (decomp E K w) L')
      (_ : MulDistribMulAction (decomp E K w) (↥L')ˣ)
      (Φ : w.adicCompletion K ≃+* L'),
      (∀ (g : decomp E K w) (x : ℚ_[q]), g • algebraMap ℚ_[q] L' x = algebraMap ℚ_[q] L' x) ∧
      (∀ (g : decomp E K w) (u : (↥L')ˣ), ((g • u : (↥L')ˣ) : L') = g • (u : L')) ∧
      (∀ (g : decomp E K w) (x : w.adicCompletion K), Φ (g • x) = g • Φ x) ∧
      ((q : ℕ) : 𝓞 K) ∈ w.asIdeal := by p2m_exact_reverting @_root_.P2MW.S_NumberField_PlaceDecomp_exists_localLevel_ringEquiv_adicCompletion.solution
