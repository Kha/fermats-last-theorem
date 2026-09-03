import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_isDomain_tensorProduct_sections_of_geometricallyIntegral

universe u

open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.isDomain_tensorProduct_sections_of_geometricallyIntegral
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [GeometricallyIntegral c] (U : C.Opens) (hU : IsAffineOpen U)
    (K : Type u) [Field K] [Algebra R K]
    (hne : letI := Scheme.TwoAffineOpenCover.algebraOfHom c U; Nontrivial (K ⊗[R] Γ(C, U))) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom c U
    IsDomain (K ⊗[R] Γ(C, U)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_isDomain_tensorProduct_sections_of_geometricallyIntegral.solution
