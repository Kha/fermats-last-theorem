import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_M4aHerbrand_GenuineDescent
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_diagonal_normString_eq_toTensorGL_globalPoints_of_baseChangeGL_eq_globalPoints

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions

attribute [local instance] NumberField.AdelicHaar.glBorel AutomorphicForm.centralizerBorel
  AutomorphicForm.twistedCentralizerBorel

theorem AutomorphicForm.exists_diagonal_normString_eq_toTensorGL_globalPoints_of_baseChangeGL_eq_globalPoints
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (t : GL (Fin 2) L) (ht₁ : (t : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) (ht₂ : (t : Matrix (Fin 2) (Fin 2) L) 0 1 = 0)
    (δ : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))
    (hδ : AutomorphicForm.baseChangeGL K L δ = AutomorphicForm.globalPoints (𝓞 L) L t) :
    ∃ γ : GL (Fin 2) K,
      (γ : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 ∧ (γ : Matrix (Fin 2) (Fin 2) K) 0 1 = 0 ∧
      (γ : Matrix (Fin 2) (Fin 2) K) 0 0 = Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 0 0) ∧
      (γ : Matrix (Fin 2) (Fin 2) K) 1 1 = Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 1 1) ∧
      AutomorphicForm.normString K L (AdeleRing (𝓞 K) K) σ δ =
        AutomorphicForm.toTensorGL K L (AdeleRing (𝓞 K) K) (AutomorphicForm.globalPoints (𝓞 K) K γ) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_diagonal_normString_eq_toTensorGL_globalPoints_of_baseChangeGL_eq_globalPoints.solution
