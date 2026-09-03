import Mathlib
import P2M.Util
import P2M.Sol.S_LinearMap_index_range_eq_card_residueField_pow_of_associated_det_pow

set_option autoImplicit false

theorem LinearMap.index_range_eq_card_residueField_pow_of_associated_det_pow
    (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Finite (IsLocalRing.ResidueField R)]
    (M : Type) [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]
    (f : M →ₗ[R] M) (hf : Function.Injective f)
    (ϖ : R) (hϖ : Irreducible ϖ) (m : ℕ) (hdet : Associated (LinearMap.det f) (ϖ ^ m)) :
    (LinearMap.range f).toAddSubgroup.index = Nat.card (IsLocalRing.ResidueField R) ^ m := by p2m_exact_reverting @_root_.P2MW.S_LinearMap_index_range_eq_card_residueField_pow_of_associated_det_pow.solution
