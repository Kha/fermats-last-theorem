import Mathlib
import P2M.Util
import P2M.Sol.S_exists_ringHom_completeDVR_residue_eq_of_moduleFinite_int

set_option autoImplicit false

theorem exists_ringHom_completeDVR_residue_eq_of_moduleFinite_int
    (R : Type) [CommRing R] [IsDomain R] [CharZero R] [Module.Finite ℤ R]
    (p : ℕ) [Fact p.Prime] {F : Type} [Field F] [CharP F p] (π : R →+* F) :
    ∃ (O : Type) (_ : CommRing O) (_ : IsDomain O) (_ : IsDiscreteValuationRing O)
        (_ : IsAdicComplete (IsLocalRing.maximalIdeal O) O)
        (_ : Finite (IsLocalRing.ResidueField O)) (_ : CharZero O)
        (ψ : R →+* O) (F' : Type) (_ : Field F') (_ : Algebra F F')
        (ι : IsLocalRing.ResidueField O →+* F'),
      Function.Injective ψ ∧
      Ideal.comap ψ (IsLocalRing.maximalIdeal O) = RingHom.ker π ∧
      (p : O) ∈ IsLocalRing.maximalIdeal O ∧
      ∀ x, ι (IsLocalRing.residue O (ψ x)) = algebraMap F F' (π x) := by p2m_exact_reverting @_root_.P2MW.S_exists_ringHom_completeDVR_residue_eq_of_moduleFinite_int.solution
