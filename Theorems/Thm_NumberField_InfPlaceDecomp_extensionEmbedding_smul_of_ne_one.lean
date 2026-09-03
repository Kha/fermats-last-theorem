import Mathlib
import Definitions.Def_NumberField_ArchimedeanIdeleModule
import P2M.Util
import P2M.Sol.S_NumberField_InfPlaceDecomp_extensionEmbedding_smul_of_ne_one

set_option autoImplicit false
open NumberField
open scoped NumberField.InfPlaceDecomp
theorem NumberField.InfPlaceDecomp.extensionEmbedding_smul_of_ne_one (E K : Type*) [Field E] [Field K] [Algebra E K]
    (w : InfinitePlace K) (σ : NumberField.InfPlaceDecomp.decomp E K w) (hσ : σ ≠ 1) (x : w.Completion) :
    InfinitePlace.Completion.extensionEmbedding w (σ • x) =
      starRingEnd ℂ (InfinitePlace.Completion.extensionEmbedding w x) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_InfPlaceDecomp_extensionEmbedding_smul_of_ne_one.solution
