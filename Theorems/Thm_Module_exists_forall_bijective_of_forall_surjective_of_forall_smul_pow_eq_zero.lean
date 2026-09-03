import Mathlib
import P2M.Util
import P2M.Sol.S_Module_exists_forall_bijective_of_forall_surjective_of_forall_smul_pow_eq_zero
attribute [-simp] AdicCompletion.evalₐ_mapₐ AdicCompletion.mapAlgEquivOfBijective_apply AdicCompletion.levelMapₐ_mk AdicCompletion.mapₐ_of AdicCompletion.mapAlgEquiv_symm_apply AdicCompletion.mapAlgEquiv_apply AdicCompletion.evalₐ_ofLevelwiseEquiv AdicCompletion.evalₐ_levelwiseHom AdicCompletion.localizationEquiv_of AdicCompletion.evalₐ_ofLevelwiseEquiv_symm Localization.AtPrime.quotientPowEquiv_mk

set_option autoImplicit false

universe u v

open IsLocalRing

theorem Module.exists_forall_bijective_of_forall_surjective_of_forall_smul_pow_eq_zero
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (ϖ : R) (hϖ : maximalIdeal R = Ideal.span {ϖ})
    (H : ℕ → Type v) [∀ n, AddCommGroup (H n)] [∀ n, Module R (H n)]
    (φ : ∀ n, H n →ₗ[R] H (n + 1)) (hφ : ∀ n, Function.Surjective (φ n))
    (N : ℕ) (hfin : ∀ n, N ≤ n → Module.Finite R (H n))
    (htors : ∀ n, N ≤ n → ∃ k : ℕ, ∀ x : H n, ϖ ^ k • x = 0) :
    ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → Function.Bijective (φ n) := by p2m_exact_reverting @_root_.P2MW.S_Module_exists_forall_bijective_of_forall_surjective_of_forall_smul_pow_eq_zero.solution
