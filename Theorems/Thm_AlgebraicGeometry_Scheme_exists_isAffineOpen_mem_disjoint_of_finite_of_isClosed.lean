import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_exists_isAffineOpen_mem_disjoint_of_finite_of_isClosed

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.exists_isAffineOpen_mem_disjoint_of_finite_of_isClosed
    {X : Scheme.{u}} (S : Set X) (hS : S.Finite) (hcl : ∀ s ∈ S, IsClosed ({s} : Set X))
    (x : X) (hx : x ∉ S) :
    ∃ V : X.Opens, IsAffineOpen V ∧ x ∈ V ∧ Disjoint (V : Set X) S := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_exists_isAffineOpen_mem_disjoint_of_finite_of_isClosed.solution
