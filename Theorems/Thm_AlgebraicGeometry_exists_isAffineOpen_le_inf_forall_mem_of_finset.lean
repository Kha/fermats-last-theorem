import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_isAffineOpen_le_inf_forall_mem_of_finset

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.exists_isAffineOpen_le_inf_forall_mem_of_finset
    {X : Scheme.{u}} (W : X.Opens) (hW : IsAffineOpen W) (O : X.Opens) (F : Finset X)
    (hFW : ∀ x ∈ F, x ∈ W) (hFO : ∀ x ∈ F, x ∈ O) :
    ∃ W' : X.Opens, IsAffineOpen W' ∧ W' ≤ W ⊓ O ∧ ∀ x ∈ F, x ∈ W' := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_isAffineOpen_le_inf_forall_mem_of_finset.solution
