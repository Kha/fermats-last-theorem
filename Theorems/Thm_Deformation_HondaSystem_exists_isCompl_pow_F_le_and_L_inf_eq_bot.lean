import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import P2M.Util
import P2M.Sol.S_Deformation_HondaSystem_exists_isCompl_pow_F_le_and_L_inf_eq_bot

universe u

theorem Deformation.HondaSystem.exists_isCompl_pow_F_le_and_L_inf_eq_bot
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    [Algebra 𝓞 (ZMod p)] (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
    [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
    (r : ℕ) (H₁ : Deformation.HondaSystem (p : 𝓞) (Fin r → 𝓞)) :
    ∃ (Mc Met : Submodule 𝓞 (Fin r → 𝓞)) (hc : IsCompl Mc Met),

      (∀ m ∈ Mc, H₁.F m ∈ Mc ∧ H₁.V m ∈ Mc) ∧ (∀ m ∈ Met, H₁.F m ∈ Met ∧ H₁.V m ∈ Met) ∧

      (∃ N : ℕ, ∀ m ∈ Mc, ∃ y ∈ Mc, (H₁.F ^ N) m = (p : 𝓞) • y) ∧
      (∀ m ∈ Met, ∃ m' ∈ Met, H₁.F m' = m) ∧ Met ≤ LinearMap.range H₁.F ∧

      (∀ m, m ∈ Met ↔ ∀ N : ℕ, ∃ y, (H₁.F ^ N) y = m) ∧
      (∀ m, m ∈ Mc ↔ ∀ k : ℕ, ∃ N : ℕ, ∃ y, (H₁.F ^ N) m = (p : 𝓞) ^ k • y) ∧

      Module.Free 𝓞 Mc ∧ Module.Free 𝓞 Met ∧ Module.finrank 𝓞 Mc + Module.finrank 𝓞 Met = r ∧

      H₁.L ⊓ Met = ⊥ ∧

      (∀ x ∈ (H₁.L).map (Mc.subtype ∘ₗ Submodule.projectionOnto Mc Met hc),
        x ∈ LinearMap.range H₁.F →
          ∃ y ∈ (H₁.L).map (Mc.subtype ∘ₗ Submodule.projectionOnto Mc Met hc), x = (p : 𝓞) • y) ∧
      (∀ y ∈ (H₁.L).map (Mc.subtype ∘ₗ Submodule.projectionOnto Mc Met hc),
        (p : 𝓞) • y ∈ LinearMap.range H₁.F) ∧
      LinearMap.range H₁.F ⊔ (H₁.L).map (Mc.subtype ∘ₗ Submodule.projectionOnto Mc Met hc) = ⊤ := by p2m_exact_reverting @_root_.P2MW.S_Deformation_HondaSystem_exists_isCompl_pow_F_le_and_L_inf_eq_bot.solution
