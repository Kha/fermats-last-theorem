import Definitions.Def_AutomorphicForm_UnipotentQuotient
import Definitions.Def_LanglandsTunnell_DeltaLift
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_RSCarrierSplit
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_Converse_exists_isHaarMeasure_map_unipotentHaar_eq_prod_map_val
attribute [-instance] M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion M4aHerbrand.Bridge.instT2SpaceAdeleRing

set_option autoImplicit false

open NumberField AutomorphicForm MeasureTheory

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem LanglandsTunnell.Converse.exists_isHaarMeasure_map_unipotentHaar_eq_prod_map_val :
    letI : MeasurableSpace (GL (Fin 2) ℝ) := borel (GL (Fin 2) ℝ)
    ∃ (μNArch : Measure RSCarrier.realUnipotent) (μNFin : Measure RSCarrier.finUnipotent),
      μNArch.IsHaarMeasure ∧ μNFin.IsHaarMeasure ∧
        Measure.map
            (fun n : adelicUnipotent ℚ => (LanglandsTunnell.ratArchGL2 n, RSCarrier.finFactor n))
            (unipotentHaar ℚ) =
          (Measure.map Subtype.val μNArch).prod (Measure.map Subtype.val μNFin) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_Converse_exists_isHaarMeasure_map_unipotentHaar_eq_prod_map_val.solution
