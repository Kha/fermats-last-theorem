import Mathlib
import Definitions.Def_ModularCurve_UVCrossingModel
import P2M.Util
import P2M.Sol.S_IsLocalRing_exists_notMem_and_mul_eq_of_mem_valuationSubring_of_ringEquiv_adicCompletion_uvCrossingModel

set_option autoImplicit false

open ModularCurve ModularCurve.UVCrossingModel

theorem IsLocalRing.exists_notMem_and_mul_eq_of_mem_valuationSubring_of_ringEquiv_adicCompletion_uvCrossingModel
    {B : Type*} [CommRing B] [IsDomain B] [IsNoetherianRing B] [IsLocalRing B]
    {W : Type*} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    [IsAdicComplete (IsLocalRing.maximalIdeal W) W]
    (π : W) (hπ : Irreducible π) (E : ℕ) (hE : 1 ≤ E)
    (ι : AdicCompletion (IsLocalRing.maximalIdeal B) B ≃+* UVCrossingModel W (π ^ E))
    {F : Type*} [Field F] (emb : B →+* F) (hemb : Function.Injective emb)
    (V : ValuationSubring F) (hBV : ∀ b : B, emb b ∈ V)
    (P : Ideal B) (hP : ∀ b : B, b ∈ P ↔ emb b ∈ V.nonunits) (hPm : P ≠ IsLocalRing.maximalIdeal B) :
    ∀ x : F, x ∈ V → (∃ r₀ s₀ : B, s₀ ≠ 0 ∧ x * emb s₀ = emb r₀) → ∃ r s : B, s ∉ P ∧ x * emb s = emb r := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_exists_notMem_and_mul_eq_of_mem_valuationSubring_of_ringEquiv_adicCompletion_uvCrossingModel.solution
