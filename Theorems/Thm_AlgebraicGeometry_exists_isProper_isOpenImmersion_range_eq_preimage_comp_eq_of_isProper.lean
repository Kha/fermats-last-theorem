import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_isProper_isOpenImmersion_range_eq_preimage_comp_eq_of_isProper

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.exists_isProper_isOpenImmersion_range_eq_preimage_comp_eq_of_isProper
    {P Y S : Scheme.{u}} (p : P ⟶ S) (q : Y ⟶ S) [IsProper q] [IsIntegral P]
    (U : P.Opens) [QuasiCompact U.ι] (hU : (U : Set P).Nonempty)
    (g : (U : Scheme.{u}) ⟶ Y) (hg : g ≫ q = U.ι ≫ p) :
    ∃ (P' : Scheme.{u}) (β : P' ⟶ P) (s : (U : Scheme.{u}) ⟶ P') (g' : P' ⟶ Y),
      IsIntegral P' ∧ IsProper β ∧ IsOpenImmersion s ∧ s ≫ β = U.ι ∧
      Set.range s.base = β.base ⁻¹' (U : Set P) ∧ s ≫ g' = g ∧ g' ≫ q = β ≫ p := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_isProper_isOpenImmersion_range_eq_preimage_comp_eq_of_isProper.solution
