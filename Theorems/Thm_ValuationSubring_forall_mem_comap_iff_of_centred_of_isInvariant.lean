import Mathlib
import P2M.Util
import P2M.Sol.S_ValuationSubring_forall_mem_comap_iff_of_centred_of_isInvariant

set_option autoImplicit false

open scoped Pointwise

theorem ValuationSubring.forall_mem_comap_iff_of_centred_of_isInvariant
    {F : Type*} [Field F] {G : Type*} [Group G] [MulSemiringAction G F] [Fintype G] [FaithfulSMul G F]
    {B₂ B₁ E' : Type*} [CommRing B₂] [CommRing B₁] [Field E'] [Algebra B₂ B₁]
    [MulSemiringAction G B₁] [SMulCommClass G B₂ B₁] [Algebra.IsInvariant B₂ B₁ G]
    (ρ₁ : B₁ →+* F) (hρ₁G : ∀ (g : G) (b : B₁), ρ₁ (g • b) = g • ρ₁ b)
    (hint : ∀ b : B₁, IsIntegral B₂ b)
    (𝔶 : Ideal B₁) [𝔶.IsPrime]
    (P : ValuationSubring F) (hP : ∀ b, ρ₁ b ∈ P) (hPy : ∀ b, ρ₁ b ∈ P.nonunits ↔ b ∈ 𝔶)
    (huniq : ∀ P' : ValuationSubring F, (∀ b, ρ₁ b ∈ P') → (∀ b, ρ₁ b ∈ P'.nonunits ↔ b ∈ 𝔶) → P' = P)
    (θE : ↥(FixedPoints.subfield G F) →+* E') (W : ValuationSubring E')
    (hfix : ∀ (g : G) (b : B₂), g • ρ₁ (algebraMap B₂ B₁ b) = ρ₁ (algebraMap B₂ B₁ b))
    (hint₂ : ∀ b : B₂, θE ⟨ρ₁ (algebraMap B₂ B₁ b), fun g => hfix g b⟩ ∈ W)
    (hcent₂ : ∀ b : B₂, θE ⟨ρ₁ (algebraMap B₂ B₁ b), fun g => hfix g b⟩ ∈ W.nonunits ↔ algebraMap B₂ B₁ b ∈ 𝔶) :
    ∀ e : ↥(FixedPoints.subfield G F), θE e ∈ W ↔ (e : F) ∈ P := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_forall_mem_comap_iff_of_centred_of_isInvariant.solution
