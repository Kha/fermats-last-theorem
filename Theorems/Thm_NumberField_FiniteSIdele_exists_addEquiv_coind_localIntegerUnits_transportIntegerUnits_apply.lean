import Mathlib
import Definitions.Def_NumberField_FiniteSIdeleModule
import Definitions.Def_NumberField_PlaceTransport
import P2M.Util
import P2M.Sol.S_NumberField_FiniteSIdele_exists_addEquiv_coind_localIntegerUnits_transportIntegerUnits_apply

set_option autoImplicit false
open scoped NumberField.PlaceDecomp NumberField.PlaceTransport
theorem NumberField.FiniteSIdele.exists_addEquiv_coind_localIntegerUnits_transportIntegerUnits_apply (E K : Type) [Field E]
    [NumberField E] [Field K] [NumberField K] [Algebra E K] [IsGalois E K]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E)) :
    ∃ e : (Rep.coind (NumberField.FiniteSIdele.D E K v).subtype (NumberField.FiniteSIdele.localIntegerUnits E K v))
          ≃+ Additive (Π w : {w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) //
                            w.under (NumberField.RingOfIntegers E) = v}, (w.1.adicCompletionIntegers K)ˣ),
      ∀ (f : Rep.coind (NumberField.FiniteSIdele.D E K v).subtype (NumberField.FiniteSIdele.localIntegerUnits E K v))
        (y : K ≃ₐ[E] K)
        (w : {w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) // w.under (NumberField.RingOfIntegers E) = v})
        (hy : y • w.1 = NumberField.PlaceAbove.above E K v),
        NumberField.PlaceTransport.transportIntegerUnits y hy (Additive.toMul (e f) w) = Additive.toMul (f.1 y) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_FiniteSIdele_exists_addEquiv_coind_localIntegerUnits_transportIntegerUnits_apply.solution
