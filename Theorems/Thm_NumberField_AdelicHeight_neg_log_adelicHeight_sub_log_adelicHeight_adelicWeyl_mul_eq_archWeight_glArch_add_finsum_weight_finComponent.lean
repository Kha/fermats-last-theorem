import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_WeylIntertwining
import P2M.Util
import P2M.Sol.S_NumberField_AdelicHeight_neg_log_adelicHeight_sub_log_adelicHeight_adelicWeyl_mul_eq_archWeight_glArch_add_finsum_weight_finComponent

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions

theorem NumberField.AdelicHeight.neg_log_adelicHeight_sub_log_adelicHeight_adelicWeyl_mul_eq_archWeight_glArch_add_finsum_weight_finComponent
    (K : Type) [Field K] [NumberField K]
    (x : GL (Fin 2) (AdeleRing (𝓞 K) K)) :
    -Real.log (NumberField.AdelicHeight.adelicHeight K x)
        - Real.log (NumberField.AdelicHeight.adelicHeight K (AutomorphicForm.adelicWeyl (𝓞 K) K * x)) =
      (fun y : GL (Fin 2) (InfiniteAdeleRing K) =>
        -Real.log (AutomorphicForm.WindowedSiegel.archHeight K y)
          - Real.log (AutomorphicForm.WindowedSiegel.archHeight K
              (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.adelicWeyl (𝓞 K) K) * y))) (AdelicLevel.glArch (𝓞 K) K x) +
        ∑ᶠ v : HeightOneSpectrum (𝓞 K),
          AutomorphicForm.LocalWeight.weight (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K x)) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_AdelicHeight_neg_log_adelicHeight_sub_log_adelicHeight_adelicWeyl_mul_eq_archWeight_glArch_add_finsum_weight_finComponent.solution
