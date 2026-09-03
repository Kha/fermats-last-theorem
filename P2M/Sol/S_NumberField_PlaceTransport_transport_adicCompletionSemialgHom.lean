import Mathlib
import Definitions.Def_NumberField_PlaceTransport
import Definitions.Def_DedekindDomain_Completion_BaseChange
import P2M.Util
namespace P2MW.S_NumberField_PlaceTransport_transport_adicCompletionSemialgHom

set_option autoImplicit false
open scoped NumberField.PlaceTransport

theorem solution (E K : Type*) [Field E] [NumberField E]
    [Field K] [NumberField K] [Algebra E K] (σ : K ≃ₐ[E] K)
    {v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E)}
    (W W' : v.Extension (NumberField.RingOfIntegers K)) (h : σ • W.1 = W'.1) (y : v.adicCompletion E) :
    NumberField.PlaceTransport.transport σ h (W.adicCompletionSemialgHom E K y) = W'.adicCompletionSemialgHom E K y := by
  have hc1 : Continuous fun y : v.adicCompletion E => NumberField.PlaceTransport.transport σ h (W.adicCompletionSemialgHom E K y) :=
    (NumberField.PlaceTransport.continuous_transport σ h).comp
      (IsDedekindDomain.HeightOneSpectrum.Extension.adicCompletionSemialgHom_continuous E K W)
  have hc2 : Continuous (W'.adicCompletionSemialgHom E K) :=
    IsDedekindDomain.HeightOneSpectrum.Extension.adicCompletionSemialgHom_continuous E K W'
  have hdense : DenseRange (fun a : WithVal (v.valuation E) => (a : v.adicCompletion E)) :=
    (IsDedekindDomain.HeightOneSpectrum.adicCompletion.ofCompletion_surjective E v).denseRange.comp
      UniformSpace.Completion.denseRange_coe
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion.continuous_ofCompletion E v)
  have key := hdense.equalizer hc1 hc2 <| funext fun a => by
    show NumberField.PlaceTransport.transport σ h (W.adicCompletionSemialgHom E K (a : v.adicCompletion E)) =
      W'.adicCompletionSemialgHom E K (a : v.adicCompletion E)
    rw [IsDedekindDomain.HeightOneSpectrum.Extension.adicCompletionSemialgHom_coe,
      IsDedekindDomain.HeightOneSpectrum.Extension.adicCompletionSemialgHom_coe,
      NumberField.PlaceTransport.transport_coe]
    congr 2
    show (WithVal.equiv (W'.1.valuation K)).symm (σ (algebraMap E K a.ofVal)) = _
    rw [AlgEquiv.commutes]
  exact congrFun key y
