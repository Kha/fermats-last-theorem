import Mathlib
import P2M.Util
import P2M.Sol.S_HopfAlgebra_exists_etale_nonempty_bialgEquiv_baseChange_residueField_of_henselianLocalRing

set_option autoImplicit false

open scoped TensorProduct

universe u v

theorem HopfAlgebra.exists_etale_nonempty_bialgEquiv_baseChange_residueField_of_henselianLocalRing
    (R : Type u) [CommRing R] [HenselianLocalRing R]
    (E₀ : Type v) [CommRing E₀] [HopfAlgebra (IsLocalRing.ResidueField R) E₀]
    [Coalgebra.IsCocomm (IsLocalRing.ResidueField R) E₀] [Module.Finite (IsLocalRing.ResidueField R) E₀]
    [Algebra.Etale (IsLocalRing.ResidueField R) E₀] :
    ∃ (E : Type (max u v)) (_ : CommRing E) (_ : HopfAlgebra R E) (_ : Coalgebra.IsCocomm R E)
      (_ : Module.Free R E) (_ : Module.Finite R E),
      Algebra.Etale R E ∧
      Nonempty (IsLocalRing.ResidueField R ⊗[R] E ≃ₐc[IsLocalRing.ResidueField R] E₀) := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_exists_etale_nonempty_bialgEquiv_baseChange_residueField_of_henselianLocalRing.solution
