import Mathlib
import Definitions.Def_NumberField_InfinitePlaceTransport
import P2M.Util
namespace P2MW.S_NumberField_InfinitePlaceTransport_transport_one

set_option autoImplicit false

theorem solution (E K : Type*) [Field E] [Field K] [Algebra E K]
    (w : NumberField.InfinitePlace K) (h : (1 : K ≃ₐ[E] K) • w = w) :
    NumberField.InfinitePlaceTransport.transport (1 : K ≃ₐ[E] K) h = RingEquiv.refl w.Completion := by
  apply RingEquiv.ext
  intro x
  rw [RingEquiv.refl_apply]
  refine NumberField.InfinitePlace.Completion.induction_on _ x
    (isClosed_eq (NumberField.InfinitePlaceTransport.continuous_transport (1 : K ≃ₐ[E] K) h) continuous_id)
    fun a => ?_
  change NumberField.InfinitePlaceTransport.transport (1 : K ≃ₐ[E] K) h (a : w.Completion) = (a : w.Completion)
  rw [NumberField.InfinitePlaceTransport.transport_coe]
  rfl
