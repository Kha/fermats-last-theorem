import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_WeylIntertwining
import P2M.Util
import P2M.Sol.S_NumberField_AdelicHeight_neg_log_adelicHeight_baseChangeGL_sub_log_adelicHeight_adelicWeyl_mul_eq_archWeight_tensorArch_add_finsum_semiLocalWeight_tensorPlace

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions

theorem NumberField.AdelicHeight.neg_log_adelicHeight_baseChangeGL_sub_log_adelicHeight_adelicWeyl_mul_eq_archWeight_tensorArch_add_finsum_semiLocalWeight_tensorPlace
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (x : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) :
    -Real.log (NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.baseChangeGL K L x))
        - Real.log (NumberField.AdelicHeight.adelicHeight L
            (AutomorphicForm.adelicWeyl (𝓞 L) L * AutomorphicForm.baseChangeGL K L x)) =
      (fun y : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) =>
        -Real.log (AutomorphicForm.WindowedSiegel.archHeight L (AutomorphicForm.archIdentGL K L y))
          - Real.log (AutomorphicForm.WindowedSiegel.archHeight L
              (AdelicLevel.glArch (𝓞 L) L (AutomorphicForm.adelicWeyl (𝓞 L) L) *
                AutomorphicForm.archIdentGL K L y))) (AutomorphicForm.tensorArch K L x) +
        ∑ᶠ v : HeightOneSpectrum (𝓞 K), AutomorphicForm.semiLocalWeight K L v (AutomorphicForm.tensorPlace K L v x) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_AdelicHeight_neg_log_adelicHeight_baseChangeGL_sub_log_adelicHeight_adelicWeyl_mul_eq_archWeight_tensorArch_add_finsum_semiLocalWeight_tensorPlace.solution
