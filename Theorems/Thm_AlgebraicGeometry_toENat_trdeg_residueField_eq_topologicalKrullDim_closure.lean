import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_toENat_trdeg_residueField_eq_topologicalKrullDim_closure

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

universe u

theorem AlgebraicGeometry.toENat_trdeg_residueField_eq_topologicalKrullDim_closure
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] (x : X) :
    letI : Algebra k (X.residueField x) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.presheaf.germ ⊤ x trivial ≫ X.residue x).hom.toAlgebra
    (Cardinal.toENat (Algebra.trdeg k (X.residueField x)) : WithBot ℕ∞) =
      topologicalKrullDim ↥(closure ({x} : Set X)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_toENat_trdeg_residueField_eq_topologicalKrullDim_closure.solution
