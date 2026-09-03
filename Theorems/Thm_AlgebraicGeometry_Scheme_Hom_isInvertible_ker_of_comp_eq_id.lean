import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Definitions.Def_AlgebraicCurve_RelCartier
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Hom_isInvertible_ker_of_comp_eq_id

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Hom.isInvertible_ker_of_comp_eq_id
    {X T : Scheme.{u}} {p : X ⟶ T} [IsSeparated p] [SmoothOfRelativeDimension 1 p]
    (σ : T ⟶ X) (hσ : σ ≫ p = 𝟙 T) : σ.ker.IsInvertible := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Hom_isInvertible_ker_of_comp_eq_id.solution
