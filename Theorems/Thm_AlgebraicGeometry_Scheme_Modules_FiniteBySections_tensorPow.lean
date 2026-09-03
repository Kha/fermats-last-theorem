import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import Definitions.Def_AlgebraicGeometry_ModulesTensorPow
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_FiniteBySections_tensorPow
attribute [-simp] AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

universe u
theorem AlgebraicGeometry.Scheme.Modules.FiniteBySections.tensorPow
    {R : Type u} [CommRing R] {X : Scheme.{u}} {f : X ⟶ Spec (.of R)} [IsProper f]
    {M : X.Modules} (hM : M.FiniteBySections f) {b : ℕ} (hb : 0 < b) :
    (M.tensorPow b).FiniteBySections f := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_FiniteBySections_tensorPow.solution
