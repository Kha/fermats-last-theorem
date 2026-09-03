import Mathlib
import P2M.Util
import P2M.Sol.S_ValuationSubring_exists_ne_zero_and_div_mem_of_forall_smul_eq_imp_apply_eq

set_option autoImplicit false

universe u

open scoped Pointwise

theorem ValuationSubring.exists_ne_zero_and_div_mem_of_forall_smul_eq_imp_apply_eq
    {C : Type u} [CommRing C] [IsDomain C] [IsDiscreteValuationRing C]
    (K : Type u) [Field K] [Algebra C K] [IsFractionRing C K]
    {M : Type u} [Field M] [Algebra K M] [Algebra C M] [IsScalarTower C K M]
    [FiniteDimensional K M] [IsGalois K M]
    (V : ValuationSubring M) (hCV : ∀ c : C, algebraMap C M c ∈ V)
    (hCVmax : ∀ c : C, algebraMap C M c ∈ V.nonunits ↔ c ∈ IsLocalRing.maximalIdeal C)
    (z : M) (hz : z ≠ 0)
    (hfix : ∀ σ : M ≃ₐ[K] M, σ • V = V → σ z = z) :
    ∃ c : K, c ≠ 0 ∧ z * (algebraMap K M c)⁻¹ ∈ V ∧ algebraMap K M c * z⁻¹ ∈ V := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_exists_ne_zero_and_div_mem_of_forall_smul_eq_imp_apply_eq.solution
