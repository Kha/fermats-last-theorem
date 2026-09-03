import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_AdelicLevel
import P2M.Util
import P2M.Sol.S_NumberField_InfiniteAdeleRing_map_linearMap_eq_inv_prod_norm_archEval_det_pow_mult_smul_of_isAddHaarMeasure

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions

open scoped Classical in

theorem NumberField.InfiniteAdeleRing.map_linearMap_eq_inv_prod_norm_archEval_det_pow_mult_smul_of_isAddHaarMeasure
    (K : Type) [Field K] [NumberField K]
    (V : Type) [AddCommGroup V] [Module (InfiniteAdeleRing K) V]
    [Module.Finite (InfiniteAdeleRing K) V] [Module.Free (InfiniteAdeleRing K) V]
    [TopologicalSpace V] [IsModuleTopology (InfiniteAdeleRing K) V]
    [MeasurableSpace V] [BorelSpace V]
    (ν : Measure V) [ν.IsAddHaarMeasure]
    (T : V →ₗ[InfiniteAdeleRing K] V) (hT : IsUnit (LinearMap.det T)) :
    Measure.map T ν =
      ENNReal.ofReal ((∏ w : NumberField.InfinitePlace K,
        ‖NumberField.AdelicLevel.archEval K w (LinearMap.det T)‖ ^ w.mult)⁻¹) • ν := by p2m_exact_reverting @_root_.P2MW.S_NumberField_InfiniteAdeleRing_map_linearMap_eq_inv_prod_norm_archEval_det_pow_mult_smul_of_isAddHaarMeasure.solution
