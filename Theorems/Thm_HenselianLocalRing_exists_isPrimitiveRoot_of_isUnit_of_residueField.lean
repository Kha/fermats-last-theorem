import Mathlib
import P2M.Util
import P2M.Sol.S_HenselianLocalRing_exists_isPrimitiveRoot_of_isUnit_of_residueField

set_option autoImplicit false

open IsLocalRing Polynomial

theorem HenselianLocalRing.exists_isPrimitiveRoot_of_isUnit_of_residueField
    {A : Type*} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
    (n : ℕ) (hn : 0 < n) (hnA : IsUnit (n : A))
    (hk : ∃ ζ₀ : ResidueField A, IsPrimitiveRoot ζ₀ n) :
    ∃ ζ : A, IsPrimitiveRoot ζ n ∧ ∃ ζ₀ : ResidueField A, IsPrimitiveRoot ζ₀ n ∧ residue A ζ = ζ₀ := by p2m_exact_reverting @_root_.P2MW.S_HenselianLocalRing_exists_isPrimitiveRoot_of_isUnit_of_residueField.solution
