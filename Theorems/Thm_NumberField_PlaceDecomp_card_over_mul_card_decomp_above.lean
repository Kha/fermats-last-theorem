import Mathlib
import Definitions.Def_NumberField_PlaceAbove
import Definitions.Def_NumberField_PlaceDecompositionAction
import P2M.Util
import P2M.Sol.S_NumberField_PlaceDecomp_card_over_mul_card_decomp_above

set_option autoImplicit false
open IsDedekindDomain NumberField
theorem NumberField.PlaceDecomp.card_over_mul_card_decomp_above (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K]
    [Algebra E K] [IsGalois E K] (v : HeightOneSpectrum (𝓞 E)) :
    Nat.card {w : HeightOneSpectrum (𝓞 K) // w.under (𝓞 E) = v} *
      Nat.card (NumberField.PlaceDecomp.decomp E K (NumberField.PlaceAbove.above E K v)) = Nat.card (K ≃ₐ[E] K) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_PlaceDecomp_card_over_mul_card_decomp_above.solution
