import Mathlib
import Definitions.Def_NumberField_PlaceTransport
import P2M.Util
namespace P2MW.S_NumberField_PlaceTransport_transport_one

set_option autoImplicit false
open scoped NumberField.PlaceTransport

theorem solution (E K : Type*) [Field E] [Field K] [NumberField K] [Algebra E K]
    (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) (h : (1 : K ≃ₐ[E] K) • w = w) :
    NumberField.PlaceTransport.transport (1 : K ≃ₐ[E] K) h = RingEquiv.refl (w.adicCompletion K) := by
  apply RingEquiv.ext
  intro x
  obtain ⟨y, rfl⟩ := IsDedekindDomain.HeightOneSpectrum.adicCompletion.ofCompletion_surjective K w x
  have := UniformSpace.Completion.ext
    (f := fun y => (NumberField.PlaceTransport.transport (1 : K ≃ₐ[E] K) h
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion.ofCompletion y) : w.adicCompletion K))
    (g := fun y => (IsDedekindDomain.HeightOneSpectrum.adicCompletion.ofCompletion y : w.adicCompletion K))
    ((NumberField.PlaceTransport.continuous_transport (1 : K ≃ₐ[E] K) h).comp
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion.continuous_ofCompletion K w))
    (IsDedekindDomain.HeightOneSpectrum.adicCompletion.continuous_ofCompletion K w) fun a => by
      show NumberField.PlaceTransport.transport (1 : K ≃ₐ[E] K) h (a : w.adicCompletion K) = (a : w.adicCompletion K)
      rw [NumberField.PlaceTransport.transport_coe]; rfl
  exact congrFun this y
