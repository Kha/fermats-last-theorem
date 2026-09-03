import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_nonempty_inf_of_not_isAffine

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.TwoAffineOpenCover.nonempty_inf_of_not_isAffine
    {X : Scheme.{u}} [IrreducibleSpace X] (𝒱 : X.TwoAffineOpenCover) (hX : ¬ IsAffine X) :
    ((𝒱.U0 ⊓ 𝒱.U1 : X.Opens) : Set X).Nonempty := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_nonempty_inf_of_not_isAffine.solution
