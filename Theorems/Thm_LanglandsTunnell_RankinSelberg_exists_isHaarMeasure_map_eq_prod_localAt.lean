import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_NumberField_AdelicHaar
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_RankinSelberg_exists_isHaarMeasure_map_eq_prod_localAt
attribute [-instance] M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion M4aHerbrand.Bridge.instT2SpaceAdeleRing

set_option autoImplicit false

open NumberField AutomorphicForm MeasureTheory IsDedekindDomain

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem LanglandsTunnell.RankinSelberg.exists_isHaarMeasure_map_eq_prod_localAt
    (v : HeightOneSpectrum (𝓞 ℚ)) [SecondCountableTopology (finiteAdelicGL2Subgroup ℚ)]
    (ι : GL (Fin 2) (v.adicCompletion ℚ) →* finiteAdelicGL2Subgroup ℚ) (hι_cont : Continuous ι)
    (hι : ∀ x : GL (Fin 2) (v.adicCompletion ℚ), localAt ℚ v (ι x : AdelicGL2 (𝓞 ℚ) ℚ) = x)
    (hcomm : ∀ (x : GL (Fin 2) (v.adicCompletion ℚ)) (k : finiteAdelicGL2Subgroup ℚ),
      localAt ℚ v (k : AdelicGL2 (𝓞 ℚ) ℚ) = 1 → ι x * k = k * ι x)
    (μ : Measure (finiteAdelicGL2Subgroup ℚ)) [μ.IsHaarMeasure] :
    letI : MeasurableSpace (GL (Fin 2) (v.adicCompletion ℚ)) := borel (GL (Fin 2) (v.adicCompletion ℚ))
    ∀ (μv : Measure (GL (Fin 2) (v.adicCompletion ℚ))) [μv.IsHaarMeasure],
      ∃ μ' : Measure ((localAt ℚ v).comp (finiteAdelicGL2Subgroup ℚ).subtype).ker,
        μ'.IsHaarMeasure ∧
          Measure.map
              (fun g : finiteAdelicGL2Subgroup ℚ =>
                (localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ), g * (ι (localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ)))⁻¹))
              μ =
            μv.prod (Measure.map Subtype.val μ') := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_RankinSelberg_exists_isHaarMeasure_map_eq_prod_localAt.solution
