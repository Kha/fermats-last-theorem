import Mathlib
import P2M.Util
import P2M.Sol.S_WittVector_exists_isDiscreteValuationRing_charZero_isAdicComplete_residueField_equiv_forall_existsUnique_ringHom_of_isAlgClosed

set_option autoImplicit false

theorem WittVector.exists_isDiscreteValuationRing_charZero_isAdicComplete_residueField_equiv_forall_existsUnique_ringHom_of_isAlgClosed
    (q : ℕ) [Fact q.Prime] (kbar : Type) [Field kbar] [IsAlgClosed kbar] [CharP kbar q] :
    ∃ (O : Type) (_ : CommRing O) (_ : IsDomain O) (_ : IsDiscreteValuationRing O) (_ : CharZero O)
      (_ : Algebra ℤ_[q] O) (_ : IsAdicComplete (Ideal.span {algebraMap ℤ_[q] O (q : ℤ_[q])}) O)
      (_ : (Ideal.span {algebraMap ℤ_[q] O (q : ℤ_[q])}).IsMaximal)
      (e : IsLocalRing.ResidueField O ≃+* kbar) (ι : WittVector q (GaloisField q 2) →+* O),
      ∀ (B : Type) [CommRing B] [IsLocalRing B] [IsArtinianRing B] (ρ : B →+* kbar),
        Function.Surjective ρ → RingHom.ker ρ = IsLocalRing.maximalIdeal B →
        ∃! f : O →+* B, ρ.comp f = e.toRingHom.comp (IsLocalRing.residue O) := by p2m_exact_reverting @_root_.P2MW.S_WittVector_exists_isDiscreteValuationRing_charZero_isAdicComplete_residueField_equiv_forall_existsUnique_ringHom_of_isAlgClosed.solution
