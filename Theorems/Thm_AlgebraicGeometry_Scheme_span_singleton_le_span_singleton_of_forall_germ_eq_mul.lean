import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_span_singleton_le_span_singleton_of_forall_germ_eq_mul

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.span_singleton_le_span_singleton_of_forall_germ_eq_mul
    {X : Scheme.{u}} (W : X.affineOpens) (a b : Γ(X, (W : X.Opens)))
    (hb : ∀ (V : X.affineOpens) (h : (V : X.Opens) ≤ W), (X.presheaf.map (homOfLE h).op).hom b ∈ nonZeroDivisors Γ(X, V))
    (h : ∀ (x : ↥X) (hx : x ∈ (W : X.Opens)), ∃ u : X.presheaf.stalk x,
      (X.presheaf.germ (W : X.Opens) x hx).hom a = u * (X.presheaf.germ (W : X.Opens) x hx).hom b) :
    Ideal.span {a} ≤ Ideal.span {b} := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_span_singleton_le_span_singleton_of_forall_germ_eq_mul.solution
