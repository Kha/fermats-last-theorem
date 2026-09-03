import Mathlib
import P2M.Util
import P2M.Sol.S_IsPrimitiveRoot_exists_isDiscreteValuationRing_ringHom_pow_sub_one_eq_mul_of_charP_residueField

set_option autoImplicit false

theorem IsPrimitiveRoot.exists_isDiscreteValuationRing_ringHom_pow_sub_one_eq_mul_of_charP_residueField
    (q : ℕ) [Fact q.Prime] (hq : 3 ≤ q)
    (R : Type) [CommRing R] [IsDomain R] [CharZero R] [IsLocalRing R]
    (hchar : CharP (IsLocalRing.ResidueField R) q)
    (ζ : R) (hζ : IsPrimitiveRoot ζ q) :
    ∃ (A : Type) (_ : CommRing A) (_ : IsDomain A) (_ : IsDiscreteValuationRing A) (_ : Finite (IsLocalRing.ResidueField A))
      (ϖ : A) (_ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ}) (ε : A) (_ : IsUnit ε) (_ : ϖ ^ (q - 1) = ε * (q : A))
      (ι : A →+* R) (_ : IsLocalHom ι), ι ϖ = 1 - ζ := by p2m_exact_reverting @_root_.P2MW.S_IsPrimitiveRoot_exists_isDiscreteValuationRing_ringHom_pow_sub_one_eq_mul_of_charP_residueField.solution
