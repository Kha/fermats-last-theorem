import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_AdelicLsXi
import P2M.Util
import P2M.Sol.S_AutomorphicForm_isSigmaConjugate_adeleRing_of_normString_eq_of_normString_mem_center_of_finrank_eq_two

set_option autoImplicit false

open NumberField
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.isSigmaConjugate_adeleRing_of_normString_eq_of_normString_mem_center_of_finrank_eq_two
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (δ y : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))
    (hδ : AutomorphicForm.normString K L (AdeleRing (𝓞 K) K) σ δ ∈
      Subgroup.center (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)))
    (hN : AutomorphicForm.normString K L (AdeleRing (𝓞 K) K) σ y =
      AutomorphicForm.normString K L (AdeleRing (𝓞 K) K) σ δ) :
    AutomorphicForm.IsSigmaConjugate K L (AdeleRing (𝓞 K) K) σ δ y := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_isSigmaConjugate_adeleRing_of_normString_eq_of_normString_mem_center_of_finrank_eq_two.solution
