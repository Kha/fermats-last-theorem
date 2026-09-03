import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_flat_of_smooth_of_preconnectedSpace_of_locallyQuasiFinite_endomorphism
attribute [-instance] instTopologicallyFGOfFiniteType
attribute [-simp] RegularLocalRingQuotientAscent.dualNumberFst_apply

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.flat_of_smooth_of_preconnectedSpace_of_locallyQuasiFinite_endomorphism
    {k : Type} [Field k] {X : Scheme.{0}} {f : X ⟶ Spec (CommRingCat.of k)}
    [Smooth f] [PreconnectedSpace X]
    (h : X ⟶ X) (hov : h ≫ f = f) [LocallyQuasiFinite h] :
    Flat h := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_flat_of_smooth_of_preconnectedSpace_of_locallyQuasiFinite_endomorphism.solution
