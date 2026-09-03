import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_GodementSection
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_TwistedCommutant
import P2M.Util
import P2M.Sol.S_AutomorphicForm_measure_setOf_algebraNorm_det_sum_map_tmul_eq_zero_eq_zero_of_isUnit

set_option autoImplicit false

open MeasureTheory Filter NumberField NumberField.AdelicHaar NumberField.AdelicFourier NumberField.AdelicBox
  NumberField.TateGlobal IsDedekindDomain AutomorphicForm
open scoped TensorProduct TensorProduct.RightActions ENNReal Topology SchwartzMap

attribute [local instance] NumberField.AdelicHaar.glBorel AutomorphicForm.centralizerBorel
  AutomorphicForm.twistedCentralizerBorel

open scoped Classical

theorem AutomorphicForm.measure_setOf_algebraNorm_det_sum_map_tmul_eq_zero_eq_zero_of_isUnit
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K))
    (ι : Type) [Fintype ι] [DecidableEq ι]
    (b : ι → Matrix (Fin 2) (Fin 2) L)
    (a₀ : ι → v.adicCompletion K)
    (h1 : IsUnit (Matrix.det (∑ i : ι, (b i).map fun l : L => l ⊗ₜ[K] a₀ i :
      Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K))))
    [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]
    (μ : Measure (ι → v.adicCompletion K)) [μ.IsAddHaarMeasure] :
    μ {a : ι → v.adicCompletion K |
        Algebra.norm (v.adicCompletion K) (Matrix.det (∑ i : ι, (b i).map fun l : L => l ⊗ₜ[K] a i :
          Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K))) = 0} = 0 := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_measure_setOf_algebraNorm_det_sum_map_tmul_eq_zero_eq_zero_of_isUnit.solution
