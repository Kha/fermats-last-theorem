import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_LanglandsTunnell_CubicLambda
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_AutomorphicForm_SmoothingKernel
import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries3
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_measure_unipotentEntry_preimage_mul_eq

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory AutomorphicForm

theorem LanglandsTunnell.CubicInduction.measure_unipotentEntry_preimage_mul_eq (v : HeightOneSpectrum (𝓞 ℚ)) :
    letI := localGLBorel ℚ v
    ∀ (μN : Measure ↥(unipotentGL2Hom (R := v.adicCompletion ℚ)).range) [μN.IsHaarMeasure] (u : (v.adicCompletion ℚ)ˣ),
      μN ((fun y : ↥(unipotentGL2Hom (R := v.adicCompletion ℚ)).range =>
            ((y : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 0 1) ⁻¹'
          ((fun z => ((u⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) * z) ⁻¹'
            {z : v.adicCompletion ℚ | Valued.v z ≤ 1})) =
        (LanglandsTunnell.TateLocal.modulus ((u : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) : ENNReal) *
          μN ((fun y : ↥(unipotentGL2Hom (R := v.adicCompletion ℚ)).range =>
            ((y : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 0 1) ⁻¹'
            {z : v.adicCompletion ℚ | Valued.v z ≤ 1}) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_measure_unipotentEntry_preimage_mul_eq.solution
