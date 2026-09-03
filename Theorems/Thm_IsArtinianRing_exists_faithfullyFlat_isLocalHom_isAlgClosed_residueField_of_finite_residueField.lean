import Mathlib
import P2M.Util
import P2M.Sol.S_IsArtinianRing_exists_faithfullyFlat_isLocalHom_isAlgClosed_residueField_of_finite_residueField

set_option autoImplicit false

open IsLocalRing

theorem IsArtinianRing.exists_faithfullyFlat_isLocalHom_isAlgClosed_residueField_of_finite_residueField
    (C : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [Finite (ResidueField C)] :
    ∃ (D : Type) (_ : CommRing D) (_ : IsLocalRing D) (_ : IsArtinianRing D) (_ : Algebra C D) (ℓ : ℕ) (_ : Fact ℓ.Prime),
      Module.FaithfullyFlat C D ∧ IsLocalHom (algebraMap C D) ∧
      Ideal.map (algebraMap C D) (maximalIdeal C) = maximalIdeal D ∧
      IsAlgClosed (ResidueField D) ∧ CharP (ResidueField D) ℓ := by p2m_exact_reverting @_root_.P2MW.S_IsArtinianRing_exists_faithfullyFlat_isLocalHom_isAlgClosed_residueField_of_finite_residueField.solution
