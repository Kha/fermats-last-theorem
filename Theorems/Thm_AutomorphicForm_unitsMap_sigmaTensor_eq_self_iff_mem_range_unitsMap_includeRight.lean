import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_BaseChangePlaces
import P2M.Util
import P2M.Sol.S_AutomorphicForm_unitsMap_sigmaTensor_eq_self_iff_mem_range_unitsMap_includeRight

set_option autoImplicit false

open NumberField
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.unitsMap_sigmaTensor_eq_self_iff_mem_range_unitsMap_includeRight
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (s : (L ⊗[K] InfiniteAdeleRing K)ˣ) :
    Units.map (↑(AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ)) s = s ↔ s ∈ Set.range (Units.map ((Algebra.TensorProduct.includeRight : InfiniteAdeleRing K →ₐ[K] (L ⊗[K] InfiniteAdeleRing K)).toRingHom.toMonoidHom)) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_unitsMap_sigmaTensor_eq_self_iff_mem_range_unitsMap_includeRight.solution
