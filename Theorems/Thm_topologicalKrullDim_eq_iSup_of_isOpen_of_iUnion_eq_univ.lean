import Mathlib
import P2M.Util
import P2M.Sol.S_topologicalKrullDim_eq_iSup_of_isOpen_of_iUnion_eq_univ

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem topologicalKrullDim_eq_iSup_of_isOpen_of_iUnion_eq_univ
    {T : Type} [TopologicalSpace T] {ι : Type} (W : ι → Set T) (hW : ∀ i, IsOpen (W i))
    (hcov : ⋃ i, W i = Set.univ) :
    topologicalKrullDim T = ⨆ i, topologicalKrullDim ↥(W i) := by p2m_exact_reverting @_root_.P2MW.S_topologicalKrullDim_eq_iSup_of_isOpen_of_iUnion_eq_univ.solution
