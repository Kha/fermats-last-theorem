import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevelMap
import Definitions.Def_NumberField_LevelArithmeticModP
import Definitions.Def_NumberField_PlaceTransport
import P2M.Util
import P2M.Sol.S_NumberField_PlaceTransport_exists_equiv_placesAbove_sigma_quotient_decomp_above

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory MonoidalCategory Module IsDedekindDomain NumberField NumberField.LevelArith
open scoped Classical NumberField.LevelArith NumberField.PlaceTransport

theorem NumberField.PlaceTransport.exists_equiv_placesAbove_sigma_quotient_decomp_above
    (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K] [IsGalois E K]
    (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 E))) :
    ∃ e : ↥(NumberField.SUnits.placesAbove E K S) ≃
        Σ v : S, (K ≃ₐ[E] K) ⧸ NumberField.PlaceDecomp.decomp E K (NumberField.PlaceAbove.above E K v),
      ∀ (σ : K ≃ₐ[E] K) (w w' : ↥(NumberField.SUnits.placesAbove E K S)),
        (w' : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) = σ • (w : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) → e w' = σ • e w := by p2m_exact_reverting @_root_.P2MW.S_NumberField_PlaceTransport_exists_equiv_placesAbove_sigma_quotient_decomp_above.solution
