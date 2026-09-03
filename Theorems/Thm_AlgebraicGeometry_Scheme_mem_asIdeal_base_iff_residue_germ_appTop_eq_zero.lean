import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_mem_asIdeal_base_iff_residue_germ_appTop_eq_zero

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.Scheme.mem_asIdeal_base_iff_residue_germ_appTop_eq_zero
    {X : Scheme.{u}} {R : CommRingCat.{u}} (f : X ⟶ Spec R) (y : X) (c : R) :
    c ∈ (f.base y).asIdeal ↔
      X.residue y ((X.presheaf.germ ⊤ y trivial) (f.appTop ((Scheme.ΓSpecIso R).inv c))) = 0 := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_mem_asIdeal_base_iff_residue_germ_appTop_eq_zero.solution
