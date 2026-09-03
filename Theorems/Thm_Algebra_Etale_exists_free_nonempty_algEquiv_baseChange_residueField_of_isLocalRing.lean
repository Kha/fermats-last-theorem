import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_Etale_exists_free_nonempty_algEquiv_baseChange_residueField_of_isLocalRing

set_option autoImplicit false

open scoped TensorProduct

universe u v

theorem Algebra.Etale.exists_free_nonempty_algEquiv_baseChange_residueField_of_isLocalRing
    (R : Type u) [CommRing R] [IsLocalRing R]
    (Ebar : Type v) [CommRing Ebar] [Algebra (IsLocalRing.ResidueField R) Ebar]
    [Module.Finite (IsLocalRing.ResidueField R) Ebar] [Algebra.Etale (IsLocalRing.ResidueField R) Ebar] :
    ∃ (E : Type (max u v)) (_ : CommRing E) (_ : Algebra R E),
      Module.Finite R E ∧ Module.Free R E ∧ Algebra.Etale R E ∧
      Nonempty (IsLocalRing.ResidueField R ⊗[R] E ≃ₐ[IsLocalRing.ResidueField R] Ebar) := by p2m_exact_reverting @_root_.P2MW.S_Algebra_Etale_exists_free_nonempty_algEquiv_baseChange_residueField_of_isLocalRing.solution
