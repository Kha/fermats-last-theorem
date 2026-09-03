import Mathlib
import Definitions.Def_AlgebraicGeometry_RiemannForm
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_RiemannForm_isConstScalar_pullback_map

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.RiemannForm

theorem AlgebraicGeometry.RiemannForm.isConstScalar_pullback_map
    (k : Type) [Field k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (g : A ⟶ A) (hg : g ≫ f = f) {M : A.Modules} {σ : M ⟶ M} {c : k} (hσ : IsConstScalar f σ c) :
    IsConstScalar f ((Scheme.Modules.pullback g).map σ) c := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_RiemannForm_isConstScalar_pullback_map.solution
