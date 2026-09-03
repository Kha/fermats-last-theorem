import Mathlib
import Definitions.Def_AlgebraicGeometry_HilbertFunctor
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_HilbertFunctor_exists_point_I_eq_map

set_option autoImplicit false

open MvPolynomial AlgebraicGeometry.HilbertFunctor
open scoped TensorProduct

theorem AlgebraicGeometry.HilbertFunctor.exists_point_I_eq_map
    (n : ℕ) (h : ℕ → ℕ) (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (P : Point A n h) :
    ∃ Q : Point B n h, Q.I = P.I.map (MvPolynomial.map (algebraMap A B)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_point_I_eq_map.solution
