import Mathlib
import P2M.Util
import P2M.Sol.S_IsAdicComplete_exists_isPrimitiveRoot_of_residueField

set_option autoImplicit false

universe u

theorem IsAdicComplete.exists_isPrimitiveRoot_of_residueField
    {W : Type*} [CommRing W] [IsLocalRing W] [IsAdicComplete (IsLocalRing.maximalIdeal W) W]
    (n : ℕ) (hn : 0 < n) (hnW : IsUnit (n : W))
    (hk : ∃ ζ₀ : IsLocalRing.ResidueField W, IsPrimitiveRoot ζ₀ n) :
    ∃ ζ : W, IsPrimitiveRoot ζ n := by p2m_exact_reverting @_root_.P2MW.S_IsAdicComplete_exists_isPrimitiveRoot_of_residueField.solution
