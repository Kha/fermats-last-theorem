import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Opens_morphismProperties_inclusion_comp_of_isClosed

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory

universe u

theorem AlgebraicGeometry.Scheme.Opens.morphismProperties_inclusion_comp_of_isClosed
    {B : Type u} [CommRing B] {X : Scheme.{u}} (πX : X ⟶ Spec (CommRingCat.of B))
    (U : X.Opens) (hU : IsClosed (U : Set X)) :
    (IsSeparated πX → IsSeparated (U.ι ≫ πX)) ∧ (QuasiCompact πX → QuasiCompact (U.ι ≫ πX)) ∧
      (LocallyOfFiniteType πX → LocallyOfFiniteType (U.ι ≫ πX)) ∧ (Flat πX → Flat (U.ι ≫ πX)) ∧
      (SmoothOfRelativeDimension 1 πX → SmoothOfRelativeDimension 1 (U.ι ≫ πX)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Opens_morphismProperties_inclusion_comp_of_isClosed.solution
