import Definitions.Def_NumberField_AdelicBox
import P2M.Util
import P2M.Sol.S_NumberField_AdelicHaar_measurePreserving_mul_algebraMap_adelicAddHaar

open NumberField
attribute [local instance] NumberField.AdelicHaar.adeleBorel
theorem NumberField.AdelicHaar.measurePreserving_mul_algebraMap_adelicAddHaar
    (F : Type) [Field F] [NumberField F] (a : F) (ha : a ≠ 0) :
    MeasureTheory.MeasurePreserving (fun x => algebraMap F (AdeleRing (𝓞 F) F) a * x)
      (AdelicHaar.adelicAddHaar (𝓞 F) F) (AdelicHaar.adelicAddHaar (𝓞 F) F) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_AdelicHaar_measurePreserving_mul_algebraMap_adelicAddHaar.solution
