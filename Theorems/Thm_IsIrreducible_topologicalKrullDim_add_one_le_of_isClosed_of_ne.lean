import Mathlib
import P2M.Util
import P2M.Sol.S_IsIrreducible_topologicalKrullDim_add_one_le_of_isClosed_of_ne

set_option autoImplicit false

universe u

theorem IsIrreducible.topologicalKrullDim_add_one_le_of_isClosed_of_ne
    {X : Type u} [TopologicalSpace X] {Y Z : Set X}
    (hZ : IsIrreducible Z) (hY : IsClosed Y) (hYZ : Y ⊆ Z) (hne : Y ≠ Z) :
    topologicalKrullDim Y + 1 ≤ topologicalKrullDim Z := by p2m_exact_reverting @_root_.P2MW.S_IsIrreducible_topologicalKrullDim_add_one_le_of_isClosed_of_ne.solution
