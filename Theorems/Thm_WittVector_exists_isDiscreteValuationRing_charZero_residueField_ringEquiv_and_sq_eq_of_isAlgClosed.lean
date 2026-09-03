import Mathlib
import P2M.Util
import P2M.Sol.S_WittVector_exists_isDiscreteValuationRing_charZero_residueField_ringEquiv_and_sq_eq_of_isAlgClosed

set_option autoImplicit false

theorem WittVector.exists_isDiscreteValuationRing_charZero_residueField_ringEquiv_and_sq_eq_of_isAlgClosed
    (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [IsAlgClosed k] [CharP k p] :
    ∃ (Onr : Type) (_ : CommRing Onr) (_ : IsDomain Onr) (_ : IsDiscreteValuationRing Onr) (_ : CharZero Onr)
      (_ : Algebra ℤ_[p] Onr)
      (_ : IsAdicComplete (Ideal.span {algebraMap ℤ_[p] Onr (p : ℤ_[p])}) Onr)
      (_ : (Ideal.span {algebraMap ℤ_[p] Onr (p : ℤ_[p])}).IsMaximal)
      (e : IsLocalRing.ResidueField Onr ≃+* k)
      (O' : Type) (_ : CommRing O') (_ : IsDomain O') (_ : IsDiscreteValuationRing O') (_ : CharZero O')
      (_ : Algebra Onr O') (_ : IsAdicComplete (IsLocalRing.maximalIdeal O') O')
      (ϖ' : O') (_ : ϖ' ∈ IsLocalRing.maximalIdeal O') (_ : ϖ' * ϖ' = algebraMap Onr O' ((p : ℕ) : Onr))
      (φ' : O' →+* k),
      Function.Surjective φ' ∧ φ'.comp (algebraMap Onr O') = (e : IsLocalRing.ResidueField Onr →+* k).comp (IsLocalRing.residue Onr) := by p2m_exact_reverting @_root_.P2MW.S_WittVector_exists_isDiscreteValuationRing_charZero_residueField_ringEquiv_and_sq_eq_of_isAlgClosed.solution
