import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_OrderedAffineCover_exists_forall_le_preimage_of_compactSpace

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.Scheme.OrderedAffineCover.exists_forall_le_preimage_of_compactSpace
    {Y : Scheme.{u}} [CompactSpace Y] {n : ℕ} (X : Fin n → Scheme.{u}) (h : ∀ j, Y ⟶ X j)
    (𝒰 : ∀ j, (X j).OrderedAffineCover) :
    ∃ (𝒲 : Y.OrderedAffineCover) (lam : ∀ j, 𝒲.ι → (𝒰 j).ι),
      ∀ (j : Fin n) (w : 𝒲.ι), 𝒲.U w ≤ (h j) ⁻¹ᵁ (𝒰 j).U (lam j w) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_OrderedAffineCover_exists_forall_le_preimage_of_compactSpace.solution
