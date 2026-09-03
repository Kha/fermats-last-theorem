import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_BaseChangePlaces
import P2M.Util
import P2M.Sol.S_AutomorphicForm_isClosedEmbedding_unitsMap_includeRight

set_option autoImplicit false

open NumberField
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.isClosedEmbedding_unitsMap_includeRight
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] :
    Topology.IsClosedEmbedding ((Units.map ((Algebra.TensorProduct.includeRight : InfiniteAdeleRing K →ₐ[K] (L ⊗[K] InfiniteAdeleRing K)).toRingHom.toMonoidHom)) : (InfiniteAdeleRing K)ˣ → (L ⊗[K] InfiniteAdeleRing K)ˣ) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_isClosedEmbedding_unitsMap_includeRight.solution
