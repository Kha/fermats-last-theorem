import Mathlib
import P2M.Util
import P2M.Sol.S_IsArtinianRing_finite_of_isLocalRing_of_finite_residueField

set_option autoImplicit false

open IsLocalRing

theorem IsArtinianRing.finite_of_isLocalRing_of_finite_residueField
    (C : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [Finite (ResidueField C)] : Finite C := by p2m_exact_reverting @_root_.P2MW.S_IsArtinianRing_finite_of_isLocalRing_of_finite_residueField.solution
