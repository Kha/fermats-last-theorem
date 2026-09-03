import Mathlib
import Definitions.Def_NumberField_ArchimedeanIdeleModule
import P2M.Util
import P2M.Sol.S_NumberField_InfPlaceDecomp_card_over_mul_card_decomp_above

set_option autoImplicit false
open IsDedekindDomain NumberField
theorem NumberField.InfPlaceDecomp.card_over_mul_card_decomp_above (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K]
    [Algebra E K] [IsGalois E K] (v : InfinitePlace E) :
    Nat.card {w : InfinitePlace K // w.comap (algebraMap E K) = v} *
      Nat.card (NumberField.InfPlaceDecomp.decomp E K (NumberField.ArchIdele.above E K v)) = Nat.card (K ≃ₐ[E] K) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_InfPlaceDecomp_card_over_mul_card_decomp_above.solution
