import Mathlib
import Definitions.Def_NumberField_PlaceAbove
import Definitions.Def_NumberField_PlaceDecompositionAction
import P2M.Util
import P2M.Sol.S_NumberField_PlaceDecomp_card_over_fixedField_eq_card_orbitRel_quotient

set_option autoImplicit false
open IsDedekindDomain NumberField
theorem NumberField.PlaceDecomp.card_over_fixedField_eq_card_orbitRel_quotient (E K : Type) [Field E] [NumberField E] [Field K]
    [NumberField K] [Algebra E K] [IsGalois E K] (S : Finset (HeightOneSpectrum (𝓞 E))) (H : Subgroup (K ≃ₐ[E] K)) :
    Nat.card {u : HeightOneSpectrum (𝓞 (IntermediateField.fixedField H)) // u.under (𝓞 E) ∈ S} =
      Nat.card (MulAction.orbitRel.Quotient H
        (Σ v : S, (K ≃ₐ[E] K) ⧸ NumberField.PlaceDecomp.decomp E K (NumberField.PlaceAbove.above E K v))) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_PlaceDecomp_card_over_fixedField_eq_card_orbitRel_quotient.solution
