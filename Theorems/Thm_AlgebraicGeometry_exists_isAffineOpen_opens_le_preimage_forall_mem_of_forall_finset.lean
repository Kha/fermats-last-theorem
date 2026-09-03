import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_isAffineOpen_opens_le_preimage_forall_mem_of_forall_finset

set_option autoImplicit false

universe u

p2m_open "CategoryTheory AlgebraicGeometry~exists_isAffineOpen_le_inf_forall_mem_of_finset"

theorem AlgebraicGeometry.exists_isAffineOpen_opens_le_preimage_forall_mem_of_forall_finset
    {X : Scheme.{u}}
    (hAF : ∀ G : Finset X, ∃ W : X.Opens, IsAffineOpen W ∧ ∀ x ∈ G, x ∈ W)
    (U O : X.Opens) (F : Finset ↥U) (hFO : ∀ x ∈ F, U.ι.base x ∈ O) :
    ∃ W : (U : Scheme.{u}).Opens, IsAffineOpen W ∧ W ≤ U.ι ⁻¹ᵁ O ∧ ∀ x ∈ F, x ∈ W := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_isAffineOpen_opens_le_preimage_forall_mem_of_forall_finset.solution
