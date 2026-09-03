import Mathlib
import Definitions.Def_NumberField_ArchimedeanIdeleModule
import P2M.Util
import P2M.Sol.S_NumberField_InfPlaceDecomp_card_infinitePlace_fixedField_eq_card_orbitRel_quotient

set_option autoImplicit false
open IsDedekindDomain NumberField
theorem NumberField.InfPlaceDecomp.card_infinitePlace_fixedField_eq_card_orbitRel_quotient (E K : Type) [Field E] [NumberField E]
    [Field K] [NumberField K] [Algebra E K] [IsGalois E K] (H : Subgroup (K ≃ₐ[E] K)) :
    Nat.card (InfinitePlace (IntermediateField.fixedField H)) =
      Nat.card (MulAction.orbitRel.Quotient H
        (Σ v : InfinitePlace E, (K ≃ₐ[E] K) ⧸ NumberField.InfPlaceDecomp.decomp E K (NumberField.ArchIdele.above E K v))) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_InfPlaceDecomp_card_infinitePlace_fixedField_eq_card_orbitRel_quotient.solution
