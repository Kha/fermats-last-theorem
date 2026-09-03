import Mathlib
import P2M.Util
import P2M.Sol.S_IsIntegrallyClosed_exists_notMem_and_mul_eq_of_mem_valuationSubring_of_ringKrullDim_le_two

set_option autoImplicit false

theorem IsIntegrallyClosed.exists_notMem_and_mul_eq_of_mem_valuationSubring_of_ringKrullDim_le_two
    {B : Type*} [CommRing B] [IsDomain B] [IsNoetherianRing B] [IsLocalRing B] [IsIntegrallyClosed B]
    (hdim : ringKrullDim B ≤ 2)
    {F : Type*} [Field F] (emb : B →+* F) (hemb : Function.Injective emb)
    (V : ValuationSubring F) (hBV : ∀ b : B, emb b ∈ V)
    (P : Ideal B) (hP : ∀ b : B, b ∈ P ↔ emb b ∈ V.nonunits) (hPm : P ≠ IsLocalRing.maximalIdeal B) :
    ∀ x : F, x ∈ V → (∃ r₀ s₀ : B, s₀ ≠ 0 ∧ x * emb s₀ = emb r₀) → ∃ r s : B, s ∉ P ∧ x * emb s = emb r := by p2m_exact_reverting @_root_.P2MW.S_IsIntegrallyClosed_exists_notMem_and_mul_eq_of_mem_valuationSubring_of_ringKrullDim_le_two.solution
