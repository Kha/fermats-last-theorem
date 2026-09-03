import Mathlib
import Definitions.Def_NumberField_PlaceTransport
import P2M.Util
namespace P2MW.S_NumberField_PlaceTransport_transport_trans_transport

set_option autoImplicit false
open scoped NumberField.PlaceTransport

theorem solution (E K : Type*) [Field E] [Field K] [NumberField K] [Algebra E K]
    (σ τ : K ≃ₐ[E] K) {w w' w'' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)}
    (h₁ : τ • w = w') (h₂ : σ • w' = w'') (h₃ : (σ * τ) • w = w'') :
    (NumberField.PlaceTransport.transport τ h₁).trans (NumberField.PlaceTransport.transport σ h₂)
      = NumberField.PlaceTransport.transport (σ * τ) h₃ := by
  apply RingEquiv.ext
  intro x
  obtain ⟨x, rfl⟩ := IsDedekindDomain.HeightOneSpectrum.adicCompletion.ofCompletion_surjective K w x
  have := UniformSpace.Completion.ext
    (f := fun y => NumberField.PlaceTransport.transport σ h₂ (NumberField.PlaceTransport.transport τ h₁
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion.ofCompletion y : w.adicCompletion K)))
    (g := fun y => NumberField.PlaceTransport.transport (σ * τ) h₃
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion.ofCompletion y : w.adicCompletion K))
    ((NumberField.PlaceTransport.continuous_transport σ h₂).comp
      ((NumberField.PlaceTransport.continuous_transport τ h₁).comp
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion.continuous_ofCompletion K w)))
    ((NumberField.PlaceTransport.continuous_transport (σ * τ) h₃).comp
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion.continuous_ofCompletion K w)) fun a => by
      show NumberField.PlaceTransport.transport σ h₂ (NumberField.PlaceTransport.transport τ h₁ (a : w.adicCompletion K))
        = NumberField.PlaceTransport.transport (σ * τ) h₃ (a : w.adicCompletion K)
      rw [NumberField.PlaceTransport.transport_coe, NumberField.PlaceTransport.transport_coe,
        NumberField.PlaceTransport.transport_coe]
      rfl
  exact congrFun this x
