import Mathlib
import P2M.Util
import P2M.Sol.S_HenselianLocalRing_exists_isPrimitiveRoot_of_pow_sq_sub_one_eq

set_option autoImplicit false

open IsLocalRing

theorem HenselianLocalRing.exists_isPrimitiveRoot_of_pow_sq_sub_one_eq
    (q : ℕ) [hq : Fact q.Prime]
    (A : Type*) [CommRing A] [IsDomain A] [IsLocalRing A] [HenselianLocalRing A]
    [IsAlgClosed (ResidueField A)]
    (hqA : (q : A) ∈ maximalIdeal A) (hq0 : (q : A) ≠ 0)
    (π : A) (hπ : π ^ (q ^ 2 - 1) = (q : A)) :
    ∃ ζ : A, IsPrimitiveRoot ζ q := by p2m_exact_reverting @_root_.P2MW.S_HenselianLocalRing_exists_isPrimitiveRoot_of_pow_sq_sub_one_eq.solution
