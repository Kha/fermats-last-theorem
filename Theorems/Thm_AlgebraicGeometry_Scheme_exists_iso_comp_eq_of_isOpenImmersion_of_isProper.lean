import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_exists_iso_comp_eq_of_isOpenImmersion_of_isProper

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.exists_iso_comp_eq_of_isOpenImmersion_of_isProper
    {K : Type u} [Field K] {C C' : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of K)) (c' : C' ⟶ Spec (CommRingCat.of K))
    [IsIntegral C] [IsProper c] [SmoothOfRelativeDimension 1 c]
    [IsIntegral C'] [IsProper c'] [Smooth c']
    (U : C.Opens) (hU : (U : Set C).Nonempty)
    (j : (U : Scheme.{u}) ⟶ C') [IsOpenImmersion j] (hj : j ≫ c' = U.ι ≫ c) :
    ∃ e : C ≅ C', e.hom ≫ c' = c ∧ U.ι ≫ e.hom = j := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_exists_iso_comp_eq_of_isOpenImmersion_of_isProper.solution
