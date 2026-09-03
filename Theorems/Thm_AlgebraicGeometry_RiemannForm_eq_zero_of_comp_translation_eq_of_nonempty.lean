import Mathlib
import Definitions.Def_AlgebraicGeometry_RiemannForm
import Definitions.Def_JacJ1Iface
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_RiemannForm_eq_zero_of_comp_translation_eq_of_nonempty

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.RiemannForm

theorem AlgebraicGeometry.RiemannForm.eq_zero_of_comp_translation_eq_of_nonempty
    (k : Type) [Field k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative)
    {Z : Scheme.{0}} (hZ : Nonempty ↥Z) (v : Z ⟶ A) (P : L.AlgPoints hc k)
    (h : v ≫ translation f L (RelativeGroupLaw.AlgPoints.toPoint P) = v) :
    P = 0 := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_RiemannForm_eq_zero_of_comp_translation_eq_of_nonempty.solution
