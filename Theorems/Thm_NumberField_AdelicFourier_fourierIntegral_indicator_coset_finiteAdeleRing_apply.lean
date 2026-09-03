import Definitions.Def_NumberField_AdelicFourier
import Definitions.Def_NumberField_AdelicBox
import P2M.Util
import P2M.Sol.S_NumberField_AdelicFourier_fourierIntegral_indicator_coset_finiteAdeleRing_apply

set_option autoImplicit false

open NumberField NumberField.AdelicFourier NumberField.AdelicBox IsDedekindDomain MeasureTheory
open scoped Classical in

theorem NumberField.AdelicFourier.fourierIntegral_indicator_coset_finiteAdeleRing_apply
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)]
    (ν : MeasureTheory.Measure (FiniteAdeleRing (𝓞 F) F)) [ν.IsAddHaarMeasure]
    {ψf : AddChar (FiniteAdeleRing (𝓞 F) F) ℂ} (hψf : Continuous ψf)
    (y u w : FiniteAdeleRing (𝓞 F) F) :
    fourierIntegral ψf ν (((fun z ↦ y + u * z) '' integralFiniteAdeles (𝓞 F) F).indicator 1) w
      = ψf (-(y * w)) * ((ν ((fun z ↦ y + u * z) '' integralFiniteAdeles (𝓞 F) F)).toReal : ℂ)
        * (if ∀ z ∈ integralFiniteAdeles (𝓞 F) F, ψf (u * w * z) = 1 then 1 else 0) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_AdelicFourier_fourierIntegral_indicator_coset_finiteAdeleRing_apply.solution
