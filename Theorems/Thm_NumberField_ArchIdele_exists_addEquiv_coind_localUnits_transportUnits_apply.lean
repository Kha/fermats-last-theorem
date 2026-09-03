import Mathlib
import Definitions.Def_NumberField_ArchimedeanIdeleModule
import Definitions.Def_NumberField_InfinitePlaceTransport
import P2M.Util
import P2M.Sol.S_NumberField_ArchIdele_exists_addEquiv_coind_localUnits_transportUnits_apply

set_option autoImplicit false
theorem NumberField.ArchIdele.exists_addEquiv_coind_localUnits_transportUnits_apply (E K : Type) [Field E] [NumberField E]
    [Field K] [NumberField K] [Algebra E K] [IsGalois E K] (v : NumberField.InfinitePlace E) :
    ∃ e : (Rep.coind (NumberField.InfPlaceDecomp.decomp E K (NumberField.ArchIdele.above E K v)).subtype
          (NumberField.InfPlaceDecomp.localUnits E K (NumberField.ArchIdele.above E K v))) ≃+
        Additive (Π w : {w : NumberField.InfinitePlace K // w.comap (algebraMap E K) = v}, (w.1.Completion)ˣ),
      ∀ (f : Rep.coind (NumberField.InfPlaceDecomp.decomp E K (NumberField.ArchIdele.above E K v)).subtype
          (NumberField.InfPlaceDecomp.localUnits E K (NumberField.ArchIdele.above E K v)))
        (y : K ≃ₐ[E] K) (w : {w : NumberField.InfinitePlace K // w.comap (algebraMap E K) = v})
        (hy : y • w.1 = NumberField.ArchIdele.above E K v),
        NumberField.InfinitePlaceTransport.transportUnits y hy (Additive.toMul (e f) w) = Additive.toMul (f.1 y) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_ArchIdele_exists_addEquiv_coind_localUnits_transportUnits_apply.solution
