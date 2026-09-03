import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_WeylIntertwining
import P2M.Util
import P2M.Sol.S_AutomorphicForm_weight_localCentralizer_mul_and_semiLocalWeight_twistedCentralizer_mul_of_diagonal

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.weight_localCentralizer_mul_and_semiLocalWeight_twistedCentralizer_mul_of_diagonal
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] (σ : L ≃ₐ[K] L) (v : HeightOneSpectrum (𝓞 K)) :
    (∀ γv : GL (Fin 2) (v.adicCompletion K),
      (γv : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 0 = 0 →
      (γv : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 1 = 0 →
      AutomorphicForm.IsRegularSemisimple γv →
      ∀ t : AutomorphicForm.localCentralizer K v γv, ∀ x : GL (Fin 2) (v.adicCompletion K),
        AutomorphicForm.LocalWeight.weight ((t : GL (Fin 2) (v.adicCompletion K)) * x) =
          AutomorphicForm.LocalWeight.weight x) ∧
    (∀ δv : GL (Fin 2) (L ⊗[K] v.adicCompletion K),
      (δv : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 1 0 = 0 →
      (δv : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 0 1 = 0 →
      AutomorphicForm.IsRegularSemisimple (AutomorphicForm.normString K L (v.adicCompletion K) σ δv) →
      ∀ t : AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δv,
        ∀ x : GL (Fin 2) (L ⊗[K] v.adicCompletion K),
          AutomorphicForm.semiLocalWeight K L v ((t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) * x) =
            AutomorphicForm.semiLocalWeight K L v x) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_weight_localCentralizer_mul_and_semiLocalWeight_twistedCentralizer_mul_of_diagonal.solution
