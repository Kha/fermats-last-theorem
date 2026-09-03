import Mathlib
import P2M.Util
import P2M.Sol.S_Module_forall_baseChange_localization_eq_zero_and_mem_range_of_forall_baseChange_field

set_option autoImplicit false

universe u

open TensorProduct

theorem Module.forall_baseChange_localization_eq_zero_and_mem_range_of_forall_baseChange_field
    (S : Type u) [CommRing S] (𝔪 : Ideal S) [𝔪.IsMaximal] (n : ℕ)
    (K : ℕ → Type u) [∀ i, AddCommGroup (K i)] [∀ i, Module S (K i)]
    [∀ i, Module.Finite S (K i)] [∀ i, Module.Projective S (K i)]
    (hbdd : ∀ i, n < i → Subsingleton (K i))
    (δ : ∀ i, K i →ₗ[S] K (i + 1)) (hdd : ∀ i, δ (i + 1) ∘ₗ δ i = 0)
    (B : Type u) [Field B] [Algebra S B] (hB : Function.Surjective (algebraMap S B))
    (h𝔪 : 𝔪 ≤ RingHom.ker (algebraMap S B))
    (h0 : ∀ z : B ⊗[S] K 0, (δ 0).baseChange B z = 0 → z = 0)
    (hS : ∀ (i : ℕ) (z : B ⊗[S] K (i + 1)), (δ (i + 1)).baseChange B z = 0 →
      z ∈ LinearMap.range ((δ i).baseChange B)) :
    (∀ z : Localization.AtPrime 𝔪 ⊗[S] K 0, (δ 0).baseChange (Localization.AtPrime 𝔪) z = 0 → z = 0) ∧
      ∀ (i : ℕ) (z : Localization.AtPrime 𝔪 ⊗[S] K (i + 1)),
        (δ (i + 1)).baseChange (Localization.AtPrime 𝔪) z = 0 →
          z ∈ LinearMap.range ((δ i).baseChange (Localization.AtPrime 𝔪)) := by p2m_exact_reverting @_root_.P2MW.S_Module_forall_baseChange_localization_eq_zero_and_mem_range_of_forall_baseChange_field.solution
