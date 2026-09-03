import Mathlib
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_IsClosedImmersion_exists_comp_eq_of_exists_comp_eq_comp_of_ker_eq_bot

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem solution
    {T T' A Z : Scheme.{0}} (π : T' ⟶ T) (hπ : π.ker = ⊥) (y : T ⟶ A) (ι : Z ⟶ A) [IsClosedImmersion ι]
    (h : ∃ z' : T' ⟶ Z, z' ≫ ι = π ≫ y) :
    ∃ z : T ⟶ Z, z ≫ ι = y := by
  obtain ⟨z', hz'⟩ := h
  have hle : ι.ker ≤ y.ker := by
    calc ι.ker ≤ (z' ≫ ι).ker := Scheme.Hom.le_ker_comp z' ι
      _ = (π ≫ y).ker := by rw [hz']
      _ = (π.ker).map y := Scheme.Hom.ker_comp π y
      _ = y.ker := by rw [hπ, Scheme.IdealSheafData.map_bot]
  exact ⟨IsClosedImmersion.lift ι y hle, IsClosedImmersion.lift_fac ι y hle⟩
