import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_Etale_existsUnique_algHom_baseChange_residueField_eq_of_moduleFinite_of_henselianLocalRing

set_option autoImplicit false

open scoped TensorProduct

universe u v w

theorem Algebra.Etale.existsUnique_algHom_baseChange_residueField_eq_of_moduleFinite_of_henselianLocalRing
    (R : Type u) [CommRing R] [HenselianLocalRing R]
    (O : Type v) [CommRing O] [Algebra R O] [Module.Finite R O] [Algebra.Etale R O]
    (C : Type w) [CommRing C] [Algebra R C] [Module.Finite R C]
    (ψbar : IsLocalRing.ResidueField R ⊗[R] O →ₐ[IsLocalRing.ResidueField R] IsLocalRing.ResidueField R ⊗[R] C) :
    ∃! ψ : O →ₐ[R] C,
      Algebra.TensorProduct.map (AlgHom.id (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField R)) ψ = ψbar := by p2m_exact_reverting @_root_.P2MW.S_Algebra_Etale_existsUnique_algHom_baseChange_residueField_eq_of_moduleFinite_of_henselianLocalRing.solution
