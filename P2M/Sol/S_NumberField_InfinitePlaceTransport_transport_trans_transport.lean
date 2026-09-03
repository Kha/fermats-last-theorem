import Mathlib
import Definitions.Def_NumberField_InfinitePlaceTransport
import P2M.Util
namespace P2MW.S_NumberField_InfinitePlaceTransport_transport_trans_transport

set_option autoImplicit false

theorem solution (E K : Type*) [Field E] [Field K] [Algebra E K]
    (σ τ : K ≃ₐ[E] K) {w w' w'' : NumberField.InfinitePlace K}
    (h₁ : τ • w = w') (h₂ : σ • w' = w'') (h₃ : (σ * τ) • w = w'') :
    (NumberField.InfinitePlaceTransport.transport τ h₁).trans (NumberField.InfinitePlaceTransport.transport σ h₂)
      = NumberField.InfinitePlaceTransport.transport (σ * τ) h₃ := by
  apply RingEquiv.ext
  intro x
  show NumberField.InfinitePlaceTransport.transport σ h₂ (NumberField.InfinitePlaceTransport.transport τ h₁ x)
    = NumberField.InfinitePlaceTransport.transport (σ * τ) h₃ x
  refine NumberField.InfinitePlace.Completion.induction_on _ x
    (isClosed_eq
      ((NumberField.InfinitePlaceTransport.continuous_transport σ h₂).comp
        (NumberField.InfinitePlaceTransport.continuous_transport τ h₁))
      (NumberField.InfinitePlaceTransport.continuous_transport (σ * τ) h₃))
    fun a => ?_
  change NumberField.InfinitePlaceTransport.transport σ h₂ (NumberField.InfinitePlaceTransport.transport τ h₁ (a : w.Completion))
    = NumberField.InfinitePlaceTransport.transport (σ * τ) h₃ (a : w.Completion)
  rw [NumberField.InfinitePlaceTransport.transport_coe, NumberField.InfinitePlaceTransport.transport_coe,
    NumberField.InfinitePlaceTransport.transport_coe]
  rfl
