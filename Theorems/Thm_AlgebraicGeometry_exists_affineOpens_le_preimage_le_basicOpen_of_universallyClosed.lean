import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_affineOpens_le_preimage_le_basicOpen_of_universallyClosed

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.exists_affineOpens_le_preimage_le_basicOpen_of_universallyClosed
    {X Y : Scheme.{u}} (p : X ⟶ Y) [UniversallyClosed p] (U : Y.Opens) (y : Y) (hy : y ∈ U)
    (s : Γ(X, p ⁻¹ᵁ U)) (hs : ∀ x : X, p.base x = y → x ∈ X.basicOpen s) :
    ∃ V : Y.affineOpens, y ∈ V.1 ∧ V.1 ≤ U ∧ p ⁻¹ᵁ V.1 ≤ X.basicOpen s := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_affineOpens_le_preimage_le_basicOpen_of_universallyClosed.solution
