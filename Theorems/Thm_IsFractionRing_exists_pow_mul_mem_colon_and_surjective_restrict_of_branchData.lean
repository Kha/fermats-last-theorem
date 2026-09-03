import Mathlib
import P2M.Util
import P2M.Sol.S_IsFractionRing_exists_pow_mul_mem_colon_and_surjective_restrict_of_branchData

set_option autoImplicit false

universe u v

theorem IsFractionRing.exists_pow_mul_mem_colon_and_surjective_restrict_of_branchData
    {B : Type u} [CommRing B] [IsDomain B] [IsNoetherianRing B]
    {F : Type v} [Field F] [Algebra B F] [IsFractionRing B F]
    {ι : Type u} [Fintype ι]
    (𝔪 : ι → Ideal B) (h𝔪 : ∀ i, (𝔪 i).IsMaximal) (hinj : Function.Injective 𝔪)
    (t : ι → B) (ht : ∀ i, t i ∈ 𝔪 i) (ht0 : ∀ i, t i ≠ 0)
    (I : ι → Ideal B)
    (hI : ∀ i (a : B), a ∈ I i ↔ ∃ s : B, s ∉ 𝔪 i ∧ s * a ∈ Ideal.span {t i})
    (hle : ∀ i (P : Ideal B), P.IsPrime → I i ≤ P → P ≤ 𝔪 i)
    (n : ℕ) :

    (∀ (x : B) (g : F),
      (∀ 𝔭 : Ideal B, 𝔭.IsPrime → x ∉ 𝔭 → ∃ s : B, s ∉ 𝔭 ∧
        ∀ a ∈ (∏ i, I i) ^ n, ∃ b : B, g * algebraMap B F a * algebraMap B F s = algebraMap B F b) →
      ∃ k : ℕ, ∀ a ∈ (∏ i, I i) ^ n, ∃ b : B, algebraMap B F x ^ k * g * algebraMap B F a = algebraMap B F b) ∧

    (∀ e : ι → B, ∃ g : F, (∀ a ∈ (∏ i, I i) ^ (n + 1), ∃ b : B, g * algebraMap B F a = algebraMap B F b) ∧
      ∀ i, ∃ (s c : B), s ∉ 𝔪 i ∧ c ∈ I i ∧
        (g * algebraMap B F (t i) ^ (n + 1) - algebraMap B F (e i)) * algebraMap B F s = algebraMap B F c) ∧
    (∀ g : F, (∀ a ∈ (∏ i, I i) ^ (n + 1), ∃ b : B, g * algebraMap B F a = algebraMap B F b) →
      ((∀ i, ∃ (s c : B), s ∉ 𝔪 i ∧ c ∈ I i ∧ g * algebraMap B F (t i) ^ (n + 1) * algebraMap B F s = algebraMap B F c) ↔
        ∀ a ∈ (∏ i, I i) ^ n, ∃ b : B, g * algebraMap B F a = algebraMap B F b)) := by p2m_exact_reverting @_root_.P2MW.S_IsFractionRing_exists_pow_mul_mem_colon_and_surjective_restrict_of_branchData.solution
