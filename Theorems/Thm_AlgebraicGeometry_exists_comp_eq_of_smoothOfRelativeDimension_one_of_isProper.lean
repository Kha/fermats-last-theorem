import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_comp_eq_of_smoothOfRelativeDimension_one_of_isProper

set_option autoImplicit false

universe u

p2m_open "CategoryTheory AlgebraicGeometry~exists_hom_comp_eq_and_comp_eq_of_isProper_of_isDiscreteValuationRing_stalk"

theorem AlgebraicGeometry.exists_comp_eq_of_smoothOfRelativeDimension_one_of_isProper
    {k : Type u} [Field k] {C Y : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of k)) [IsIntegral C] [SmoothOfRelativeDimension 1 c]
    (g : Y ⟶ Spec (CommRingCat.of k)) [IsProper g]
    (U : C.Opens) (hU : (U : Set C).Nonempty) (ψ : (U : Scheme.{u}) ⟶ Y) (hψ : ψ ≫ g = U.ι ≫ c) :
    ∃ ν : C ⟶ Y, ν ≫ g = c ∧ U.ι ≫ ν = ψ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_comp_eq_of_smoothOfRelativeDimension_one_of_isProper.solution
