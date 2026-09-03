import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import P2M.Util
import P2M.Sol.S_AutomorphicForm_semiLocalWeight_unipotentGL2_eq_finsum_log_max_and_eq_log_norm_norm_of_one_le_and_norm_baseChangeAlgEquiv_algebraMap_eq_pow

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.semiLocalWeight_unipotentGL2_eq_finsum_log_max_and_eq_log_norm_norm_of_one_le_and_norm_baseChangeAlgEquiv_algebraMap_eq_pow
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) :
    (∀ y : L ⊗[K] v.adicCompletion K,
      AutomorphicForm.semiLocalWeight K L v (AutomorphicForm.unipotentGL2 y) =
        ∑ᶠ w : v.Extension (𝓞 L),
          2 * Real.log (max 1 ‖HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v y w‖)) ∧
    (∀ y : L ⊗[K] v.adicCompletion K,
      (∀ w : v.Extension (𝓞 L), 1 ≤ ‖HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v y w‖) →
      AutomorphicForm.semiLocalWeight K L v (AutomorphicForm.unipotentGL2 y) =
        2 * Real.log ‖Algebra.norm (v.adicCompletion K) y‖) ∧
    (∀ (s : v.adicCompletion K) (w : v.Extension (𝓞 L)),
      ‖HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v
          (algebraMap (v.adicCompletion K) (L ⊗[K] v.adicCompletion K) s) w‖ =
        ‖s‖ ^ Module.finrank (v.adicCompletion K) (w.1.adicCompletion L)) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_semiLocalWeight_unipotentGL2_eq_finsum_log_max_and_eq_log_norm_norm_of_one_le_and_norm_baseChangeAlgEquiv_algebraMap_eq_pow.solution
