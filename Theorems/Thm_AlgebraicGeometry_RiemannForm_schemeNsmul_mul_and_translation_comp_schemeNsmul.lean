import Mathlib
import Definitions.Def_AlgebraicGeometry_RiemannForm
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_RiemannForm_schemeNsmul_mul_and_translation_comp_schemeNsmul

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.RiemannForm

theorem AlgebraicGeometry.RiemannForm.schemeNsmul_mul_and_translation_comp_schemeNsmul
    (k : Type) [Field k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative) (n m : ℕ) (P : L.AlgPoints hc k) :
    L.schemeNsmul (n * m) = L.schemeNsmul m ≫ L.schemeNsmul n ∧
    translation f L (RelativeGroupLaw.AlgPoints.toPoint P) ≫ L.schemeNsmul m =
      L.schemeNsmul m ≫ translation f L (RelativeGroupLaw.AlgPoints.toPoint (m • P)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_RiemannForm_schemeNsmul_mul_and_translation_comp_schemeNsmul.solution
