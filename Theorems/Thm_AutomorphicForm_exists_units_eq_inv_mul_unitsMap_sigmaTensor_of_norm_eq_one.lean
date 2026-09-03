import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_BaseChangePlaces
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_units_eq_inv_mul_unitsMap_sigmaTensor_of_norm_eq_one

set_option autoImplicit false

open NumberField
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.exists_units_eq_inv_mul_unitsMap_sigmaTensor_of_norm_eq_one
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) (hdeg : (Module.finrank K L).Prime)
    (v : (L ⊗[K] InfiniteAdeleRing K)ˣ) (hv : Algebra.norm (InfiniteAdeleRing K) (v : (L ⊗[K] InfiniteAdeleRing K)) = 1) :
    ∃ s : (L ⊗[K] InfiniteAdeleRing K)ˣ, v = s⁻¹ * Units.map (↑(AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ)) s := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_units_eq_inv_mul_unitsMap_sigmaTensor_of_norm_eq_one.solution
