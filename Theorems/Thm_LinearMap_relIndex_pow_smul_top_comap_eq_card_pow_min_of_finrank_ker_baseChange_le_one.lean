import Mathlib
import P2M.Util
import P2M.Sol.S_LinearMap_relIndex_pow_smul_top_comap_eq_card_pow_min_of_finrank_ker_baseChange_le_one

set_option autoImplicit false

open scoped TensorProduct

theorem LinearMap.relIndex_pow_smul_top_comap_eq_card_pow_min_of_finrank_ker_baseChange_le_one
    (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Finite (IsLocalRing.ResidueField R)]
    (M : Type) [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]
    (f : M →ₗ[R] M) (hf : Function.Injective f)
    (hker : Module.finrank (IsLocalRing.ResidueField R)
        (LinearMap.ker (f.baseChange (IsLocalRing.ResidueField R))) ≤ 1)
    (ϖ : R) (hϖ : Irreducible ϖ) (m : ℕ) (hdet : Associated (LinearMap.det f) (ϖ ^ m)) (s : ℕ) :
    ((Ideal.span {ϖ ^ s} • ⊤ : Submodule R M).toAddSubgroup).relIndex
        (((Ideal.span {ϖ ^ s} • ⊤ : Submodule R M).comap f).toAddSubgroup) =
      Nat.card (IsLocalRing.ResidueField R) ^ min s m := by p2m_exact_reverting @_root_.P2MW.S_LinearMap_relIndex_pow_smul_top_comap_eq_card_pow_min_of_finrank_ker_baseChange_le_one.solution
