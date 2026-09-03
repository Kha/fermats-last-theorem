import Mathlib
import Definitions.Def_AlgebraicGeometry_RiemannForm
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_RiemannForm_translation_comp_schemeNsmul_of_nsmul_eq_zero

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.RiemannForm

theorem AlgebraicGeometry.RiemannForm.translation_comp_schemeNsmul_of_nsmul_eq_zero
    (k : Type) [Field k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative)
    (P : L.AlgPoints hc k) (m : ℕ) (hP : m • P = 0) :
    translation f L (RelativeGroupLaw.AlgPoints.toPoint P) ≫ L.schemeNsmul m = L.schemeNsmul m := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_RiemannForm_translation_comp_schemeNsmul_of_nsmul_eq_zero.solution
