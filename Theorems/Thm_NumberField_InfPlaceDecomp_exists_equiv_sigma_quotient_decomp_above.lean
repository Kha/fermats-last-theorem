import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevelMap
import Definitions.Def_NumberField_LevelArithmeticModP
import Definitions.Def_NumberField_ArchimedeanIdeleModule
import P2M.Util
import P2M.Sol.S_NumberField_InfPlaceDecomp_exists_equiv_sigma_quotient_decomp_above

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory MonoidalCategory Module IsDedekindDomain NumberField NumberField.LevelArith
open scoped Classical NumberField.LevelArith

theorem NumberField.InfPlaceDecomp.exists_equiv_sigma_quotient_decomp_above
    (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K] [IsGalois E K] :
    ∃ e : NumberField.InfinitePlace K ≃
        Σ v : NumberField.InfinitePlace E, (K ≃ₐ[E] K) ⧸ NumberField.InfPlaceDecomp.decomp E K (NumberField.ArchIdele.above E K v),
      ∀ (σ : K ≃ₐ[E] K) (w : NumberField.InfinitePlace K), e (σ • w) = σ • e w := by p2m_exact_reverting @_root_.P2MW.S_NumberField_InfPlaceDecomp_exists_equiv_sigma_quotient_decomp_above.solution
