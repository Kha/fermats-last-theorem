import Mathlib
import Definitions.Def_NumberField_InfinitePlaceTransport
import Definitions.Def_NumberField_ArchimedeanIdeleModule
import P2M.Util
namespace P2MW.S_NumberField_InfinitePlaceTransport_transport_eq_actRingEquiv

set_option autoImplicit false

theorem solution (E K : Type*) [Field E] [Field K] [Algebra E K]
    (w : NumberField.InfinitePlace K) (σ : NumberField.InfPlaceDecomp.decomp E K w) (h : (σ : K ≃ₐ[E] K) • w = w) :
    NumberField.InfinitePlaceTransport.transport (σ : K ≃ₐ[E] K) h = NumberField.InfPlaceDecomp.actRingEquiv σ :=
  rfl
