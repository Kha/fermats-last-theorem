import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_AutomorphicForm_ConstantTerm
import P2M.Util
import P2M.Sol.S_AutomorphicForm_prod_norm_pow_mult_mul_lintegral_comp_linearMap_tensor_infiniteAdeleRing_eq_lintegral_of_det_eq

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions ENNReal Pointwise
open LanglandsTunnell.CubicInduction (diagUnits2)

theorem AutomorphicForm.prod_norm_pow_mult_mul_lintegral_comp_linearMap_tensor_infiniteAdeleRing_eq_lintegral_of_det_eq
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    [MeasurableSpace (L ⊗[K] InfiniteAdeleRing K)] [BorelSpace (L ⊗[K] InfiniteAdeleRing K)]
    (lam : Measure (L ⊗[K] InfiniteAdeleRing K)) [lam.IsAddHaarMeasure]
    (T : (L ⊗[K] InfiniteAdeleRing K) →ₗ[InfiniteAdeleRing K] (L ⊗[K] InfiniteAdeleRing K))
    (d : (InfiniteAdeleRing K)ˣ) (hT : LinearMap.det T = (d : InfiniteAdeleRing K))
    (G : (L ⊗[K] InfiniteAdeleRing K) → ℝ≥0∞) (hG : Measurable G) :
    ENNReal.ofReal (∏ v : InfinitePlace K, ‖(d : InfiniteAdeleRing K) v‖ ^ v.mult) * ∫⁻ ξ, G (T ξ) ∂lam =
      ∫⁻ ξ, G ξ ∂lam := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_prod_norm_pow_mult_mul_lintegral_comp_linearMap_tensor_infiniteAdeleRing_eq_lintegral_of_det_eq.solution
