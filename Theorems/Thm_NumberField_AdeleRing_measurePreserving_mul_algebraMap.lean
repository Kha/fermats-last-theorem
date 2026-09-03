import Definitions.Def_NumberField_AdelicBox
import P2M.Util
import P2M.Sol.S_NumberField_AdeleRing_measurePreserving_mul_algebraMap

open NumberField
theorem NumberField.AdeleRing.measurePreserving_mul_algebraMap (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
    (μ : MeasureTheory.Measure (AdeleRing (𝓞 F) F)) [μ.IsAddHaarMeasure] [μ.Regular]
    (a : F) (ha : a ≠ 0) :
    MeasureTheory.MeasurePreserving (fun x => algebraMap F (AdeleRing (𝓞 F) F) a * x) μ μ := by p2m_exact_reverting @_root_.P2MW.S_NumberField_AdeleRing_measurePreserving_mul_algebraMap.solution
