import Definitions.Def_NumberField_AdelicFourier
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.Algebra.Module.ZLattice.Covolume
import P2M.Util
import P2M.Sol.S_NumberField_AdelicFourier_fourierIntegral_pureTensor_eq

open NumberField NumberField.AdelicFourier NumberField.AdelicBox AutomorphicForm IsDedekindDomain MeasureTheory
open scoped Classical FourierTransform nonZeroDivisors
theorem NumberField.AdelicFourier.fourierIntegral_pureTensor_eq
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
    (μ : MeasureTheory.Measure (AdeleRing (𝓞 F) F)) [μ.IsAddHaarMeasure]
    [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)]
    (ν : MeasureTheory.Measure (FiniteAdeleRing (𝓞 F) F)) [ν.IsAddHaarMeasure]
    {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} (hψ : Continuous ψ) (hψu : ∀ x, ‖ψ x‖ = 1)
    (g : SchwartzMap (mixedEmbedding.mixedSpace F) ℂ)
    {h : FiniteAdeleRing (𝓞 F) F → ℂ}
    (hlc : IsLocallyConstant h) (hcs : HasCompactSupport h)
    (w : AdeleRing (𝓞 F) F) :
    fourierIntegral ψ μ
        (fun x ↦ g (InfiniteAdeleRing.ringEquiv_mixedSpace F x.1) * h x.2) w
      = ((μ (adelicBox F)).toReal /
          (ZLattice.covolume (mixedEmbedding.integerLattice F) MeasureTheory.volume
            * (ν (integralFiniteAdeles (𝓞 F) F)).toReal) : ℂ)
        * fourierIntegral
            (ψ.compAddMonoidHom ((AddMonoidHom.inl _ _).comp
              (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm.toAddMonoidHom))
            MeasureTheory.volume (g : mixedEmbedding.mixedSpace F → ℂ) (InfiniteAdeleRing.ringEquiv_mixedSpace F w.1)
        * fourierIntegral
            (ψ.compAddMonoidHom (AddMonoidHom.inr _ _)) ν h w.2 := by p2m_exact_reverting @_root_.P2MW.S_NumberField_AdelicFourier_fourierIntegral_pureTensor_eq.solution
