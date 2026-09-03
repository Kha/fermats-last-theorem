import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_opens_flat_morphismRestrict_and_finrank_eq_and_mem_of_ringKrullDim_le_one_of_isFinite

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.exists_opens_flat_morphismRestrict_and_finrank_eq_and_mem_of_ringKrullDim_le_one_of_isFinite
    {X Y : Scheme.{u}} (π : X ⟶ Y) [IsFinite π] [Surjective π] [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian Y]
    (hY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y)) :
    ∃ (V : Y.Opens) (d : ℕ), Flat (π ∣_ V) ∧ LocallyOfFinitePresentation (π ∣_ V) ∧
      (∀ y : V, (π ∣_ V).finrank y = d) ∧
      ∀ y : Y, ringKrullDim (Y.presheaf.stalk y) ≤ 1 → y ∈ V := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_opens_flat_morphismRestrict_and_finrank_eq_and_mem_of_ringKrullDim_le_one_of_isFinite.solution
