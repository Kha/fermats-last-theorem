import Mathlib
import Definitions.Def_AlgebraicGeometry_RiemannForm
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_RiemannForm_translation_zero_and_translation_add

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.RiemannForm

theorem AlgebraicGeometry.RiemannForm.translation_zero_and_translation_add
    (k : Type) [Field k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative) (P Q : L.AlgPoints hc k) :
    translation f L (RelativeGroupLaw.AlgPoints.toPoint (0 : L.AlgPoints hc k)) = 𝟙 A ∧
    translation f L (RelativeGroupLaw.AlgPoints.toPoint (P + Q)) =
      translation f L (RelativeGroupLaw.AlgPoints.toPoint P) ≫ translation f L (RelativeGroupLaw.AlgPoints.toPoint Q) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_RiemannForm_translation_zero_and_translation_add.solution
