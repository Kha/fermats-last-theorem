import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_Etale_existsUnique_bialgHom_baseChange_residueField_eq_of_moduleFinite_of_henselianLocalRing

set_option autoImplicit false

open scoped TensorProduct

universe u v w

theorem Algebra.Etale.existsUnique_bialgHom_baseChange_residueField_eq_of_moduleFinite_of_henselianLocalRing
    (R : Type u) [CommRing R] [HenselianLocalRing R]
    (E : Type v) [CommRing E] [Bialgebra R E] [Module.Finite R E] [Algebra.Etale R E]
    (C : Type w) [CommRing C] [Bialgebra R C] [Module.Finite R C]
    (fbar : IsLocalRing.ResidueField R ⊗[R] E →ₐc[IsLocalRing.ResidueField R] IsLocalRing.ResidueField R ⊗[R] C) :
    ∃! f : E →ₐc[R] C,
      Bialgebra.TensorProduct.map (BialgHom.id (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField R)) f = fbar := by p2m_exact_reverting @_root_.P2MW.S_Algebra_Etale_existsUnique_bialgHom_baseChange_residueField_eq_of_moduleFinite_of_henselianLocalRing.solution
