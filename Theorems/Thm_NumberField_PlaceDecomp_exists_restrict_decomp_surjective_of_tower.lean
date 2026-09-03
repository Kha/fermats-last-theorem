import Mathlib
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_ExtCitation_LocalLevelResidues
import P2M.Util
import P2M.Sol.S_NumberField_PlaceDecomp_exists_restrict_decomp_surjective_of_tower

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxSynthPendingDepth 3
open CategoryTheory IsDedekindDomain NumberField
open scoped NumberField.PlaceDecomp

theorem NumberField.PlaceDecomp.exists_restrict_decomp_surjective_of_tower
    (E K K'' : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Field K''] [NumberField K'']
    [Algebra E K] [Algebra K K''] [Algebra E K''] [IsScalarTower E K K''] [IsGalois E K''] [Normal E K]
    (w'' : HeightOneSpectrum (𝓞 K'')) :
    ∃ r : decomp E K'' w'' →* decomp E K (HeightOneSpectrum.under (𝓞 K) w''),
      Function.Surjective r ∧
      (∀ σ : decomp E K'' w'', ((r σ : decomp E K (HeightOneSpectrum.under (𝓞 K) w'')) : K ≃ₐ[E] K) =
        AlgEquiv.restrictNormalHom K (σ : K'' ≃ₐ[E] K'')) ∧
      (∀ σ : decomp E K'' w'', r σ = 1 ↔ ∀ x : K, (σ : K'' ≃ₐ[E] K'') (algebraMap K K'' x) = algebraMap K K'' x) ∧
      (∀ τ : decomp K K'' w'', ∃ σ : decomp E K'' w'',
        (σ : K'' ≃ₐ[E] K'') = AlgEquiv.restrictScalars E (τ : K'' ≃ₐ[K] K'') ∧ r σ = 1) ∧
      (∀ (σ : decomp E K'' w'') (x : (HeightOneSpectrum.under (𝓞 K) w'').adicCompletion K),
        HeightOneSpectrum.Extension.adicCompletionSemialgHom K K''
            (⟨w'', rfl⟩ : (HeightOneSpectrum.under (𝓞 K) w'').Extension (𝓞 K'')) (r σ • x) =
          σ • HeightOneSpectrum.Extension.adicCompletionSemialgHom K K''
            (⟨w'', rfl⟩ : (HeightOneSpectrum.under (𝓞 K) w'').Extension (𝓞 K'')) x) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_PlaceDecomp_exists_restrict_decomp_surjective_of_tower.solution
