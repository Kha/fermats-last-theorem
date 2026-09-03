import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafEulerChar
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_cechFinrank_unit_zero_eq_one_of_bijective

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

theorem AlgebraicGeometry.OModulePresheaf.cechFinrank_unit_zero_eq_one_of_bijective
    {R : Type u} [CommRing R] {V : Scheme.{u}} (π : V ⟶ Spec (CommRingCat.of R))
    (h : letI := Scheme.TwoAffineOpenCover.algebraOfHom π ⊤
      Function.Bijective (algebraMap R Γ(V, ⊤)))
    (K : V.OrderedAffineCover) :
    (OModulePresheaf.unit π).cechFinrank K 0 = 1 := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_cechFinrank_unit_zero_eq_one_of_bijective.solution
