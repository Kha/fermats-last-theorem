import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Opens_eq_of_forall_isAlgClosed_mem_iff_of_locallyOfFiniteType

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Opens.eq_of_forall_isAlgClosed_mem_iff_of_locallyOfFiniteType
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f]
    (U V : X.Opens)
    (h : ∀ (K : Type u) [Field K] [IsAlgClosed K] (i : k →+* K) (p : Spec (CommRingCat.of K) ⟶ X),
      p ≫ f = Spec.map (CommRingCat.ofHom i) → ∀ y : ↥(Spec (CommRingCat.of K)), (p.base y ∈ U ↔ p.base y ∈ V)) :
    U = V := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Opens_eq_of_forall_isAlgClosed_mem_iff_of_locallyOfFiniteType.solution
