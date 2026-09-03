import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_flat_image_comp_of_isDedekindDomain

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.flat_image_comp_of_isDedekindDomain
    {R : Type u} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    {X J : Scheme.{u}} (σ : X ⟶ J) [QuasiCompact σ] (f : J ⟶ Spec (CommRingCat.of R)) [Flat (σ ≫ f)] :
    Flat (σ.imageι ≫ f) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_flat_image_comp_of_isDedekindDomain.solution
