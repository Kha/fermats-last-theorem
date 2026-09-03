import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Opens_eq_top_of_forall_mem_of_le_jacobson_of_universallyClosed

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Opens.eq_top_of_forall_mem_of_le_jacobson_of_universallyClosed
    {R : Type u} [CommRing R] (I : Ideal R) (hI : I ≤ (⊥ : Ideal R).jacobson)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [UniversallyClosed f]
    (W : X.Opens) (hW : ∀ x : X, I ≤ (f.base x).asIdeal → x ∈ W) : W = ⊤ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Opens_eq_top_of_forall_mem_of_le_jacobson_of_universallyClosed.solution
