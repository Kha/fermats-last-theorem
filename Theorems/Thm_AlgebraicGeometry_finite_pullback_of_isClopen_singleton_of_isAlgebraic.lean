import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_finite_pullback_of_isClopen_singleton_of_isAlgebraic

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.finite_pullback_of_isClopen_singleton_of_isAlgebraic
    {K : Type u} [Field K] (k : Type u) [Field k] [Algebra K k] [Algebra.IsAlgebraic K k]
    {S : Scheme.{u}} (g : S ⟶ Spec (CommRingCat.of K)) [IrreducibleSpace S] [LocallyOfFiniteType g]
    (c : ↑(pullback g (Spec.map (CommRingCat.ofHom (algebraMap K k)))))
    (hc : IsClopen ({c} : Set ↑(pullback g (Spec.map (CommRingCat.ofHom (algebraMap K k)))))) :
    Finite ↑(pullback g (Spec.map (CommRingCat.ofHom (algebraMap K k)))) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_finite_pullback_of_isClopen_singleton_of_isAlgebraic.solution
