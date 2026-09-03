import Mathlib
import P2M.Util
import P2M.Sol.S_IsLocalRing_exists_isLocalRing_etale_free_residueField_algEquiv

set_option autoImplicit false

open IsLocalRing

theorem IsLocalRing.exists_isLocalRing_etale_free_residueField_algEquiv
    (R : Type) [CommRing R] [IsLocalRing R]
    (k' : Type) [Field k'] [Algebra (ResidueField R) k'] [Module.Finite (ResidueField R) k']
    [Algebra.IsSeparable (ResidueField R) k'] :
    ∃ (E : Type) (_ : CommRing E) (_ : IsLocalRing E) (_ : Algebra R E) (_ : IsLocalHom (algebraMap R E)),
      Module.Finite R E ∧ Module.Free R E ∧ Algebra.Etale R E ∧
      (maximalIdeal R).map (algebraMap R E) = maximalIdeal E ∧
      Nonempty (ResidueField E ≃ₐ[ResidueField R] k') := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_exists_isLocalRing_etale_free_residueField_algEquiv.solution
