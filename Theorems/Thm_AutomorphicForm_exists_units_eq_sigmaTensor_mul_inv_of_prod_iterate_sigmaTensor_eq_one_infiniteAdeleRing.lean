import Definitions.Def_AutomorphicForm_TwistedOrbital
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_units_eq_sigmaTensor_mul_inv_of_prod_iterate_sigmaTensor_eq_one_infiniteAdeleRing

set_option autoImplicit false

open NumberField
open scoped TensorProduct

theorem AutomorphicForm.exists_units_eq_sigmaTensor_mul_inv_of_prod_iterate_sigmaTensor_eq_one_infiniteAdeleRing
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (x : L ⊗[K] InfiniteAdeleRing K)
    (hx : ((List.range (Module.finrank K L)).map fun i =>
        (⇑(AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ))^[i] x).prod = 1) :
    ∃ y : (L ⊗[K] InfiniteAdeleRing K)ˣ,
      x = AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ (y : L ⊗[K] InfiniteAdeleRing K) * ↑y⁻¹ := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_units_eq_sigmaTensor_mul_inv_of_prod_iterate_sigmaTensor_eq_one_infiniteAdeleRing.solution
