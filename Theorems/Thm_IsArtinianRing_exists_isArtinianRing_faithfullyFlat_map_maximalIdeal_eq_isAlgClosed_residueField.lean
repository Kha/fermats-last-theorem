import Mathlib
import P2M.Util
import P2M.Sol.S_IsArtinianRing_exists_isArtinianRing_faithfullyFlat_map_maximalIdeal_eq_isAlgClosed_residueField

set_option autoImplicit false

p2m_open "IsLocalRing~exists_isNoetherianRing_faithfullyFlat_map_maximalIdeal_eq_residueField_algEquiv_of_isAlgebraic"

theorem IsArtinianRing.exists_isArtinianRing_faithfullyFlat_map_maximalIdeal_eq_isAlgClosed_residueField
    (C : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] :
    ∃ (D : Type) (_ : CommRing D) (_ : IsLocalRing D) (_ : IsArtinianRing D) (_ : Algebra C D),
      Module.FaithfullyFlat C D ∧ IsLocalHom (algebraMap C D) ∧
      Ideal.map (algebraMap C D) (maximalIdeal C) = maximalIdeal D ∧
      IsAlgClosed (ResidueField D) := by p2m_exact_reverting @_root_.P2MW.S_IsArtinianRing_exists_isArtinianRing_faithfullyFlat_map_maximalIdeal_eq_isAlgClosed_residueField.solution
