import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_toH0_bijective

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.TwoAffineOpenCover.toH0_bijective {R : Type u} [CommRing R] {X : Scheme.{u}}
    (𝒱 : X.TwoAffineOpenCover) (c : X ⟶ Spec (.of R)) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom c ⊤
    Function.Bijective (𝒱.toH0 c) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_toH0_bijective.solution
