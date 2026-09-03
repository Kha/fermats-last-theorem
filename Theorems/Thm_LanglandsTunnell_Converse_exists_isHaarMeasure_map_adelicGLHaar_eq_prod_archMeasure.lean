import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_LanglandsTunnell_DeltaLift
import Definitions.Def_LanglandsTunnell_RSCarrierSplit
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_Converse_exists_isHaarMeasure_map_adelicGLHaar_eq_prod_archMeasure
attribute [-instance] M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion M4aHerbrand.Bridge.instT2SpaceAdeleRing

set_option autoImplicit false

open NumberField AutomorphicForm MeasureTheory IsDedekindDomain

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem LanglandsTunnell.Converse.exists_isHaarMeasure_map_adelicGLHaar_eq_prod_archMeasure :
    letI : MeasurableSpace (GL (Fin 2) ℝ) := borel (GL (Fin 2) ℝ)
    ∃ μf : Measure (finiteAdelicGL2Subgroup ℚ), μf.IsHaarMeasure ∧ μf.IsMulRightInvariant ∧
      Measure.map (fun g : AdelicGL2 (𝓞 ℚ) ℚ => (LanglandsTunnell.ratArchGL2 g, RSCarrier.finFactor g))
          (AdelicHaar.adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ) =
        RSCarrier.archMeasure.prod μf := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_Converse_exists_isHaarMeasure_map_adelicGLHaar_eq_prod_archMeasure.solution
