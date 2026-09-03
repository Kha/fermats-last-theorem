import Mathlib
import P2M.Util
import P2M.Sol.S_Ideal_exists_monoidHom_inertia_residueFieldUnits_ker_iff_of_uniformizer

universe u v
theorem Ideal.exists_monoidHom_inertia_residueFieldUnits_ker_iff_of_uniformizer {B : Type u} [CommRing B] {G : Type v} [Group G]
    [MulSemiringAction G B] (𝔓 : Ideal B) [𝔓.IsMaximal] [Finite (B ⧸ 𝔓)] {ϖ : B} (hϖP : ϖ ∈ 𝔓)
    (hgen : ∀ x ∈ 𝔓, ∃ y : B, x - ϖ * y ∈ 𝔓 ^ 2) (hreg : ∀ c : B, c * ϖ ∈ 𝔓 ^ 2 → c ∈ 𝔓) :
    ∃ θ : 𝔓.inertia G →* (B ⧸ 𝔓)ˣ,
      (∀ (σ : 𝔓.inertia G) (t : B), ((θ σ : (B ⧸ 𝔓)ˣ) : B ⧸ 𝔓) = Ideal.Quotient.mk 𝔓 t ↔
        (σ : G) • ϖ - ϖ * t ∈ 𝔓 ^ 2) ∧
      (∀ σ : 𝔓.inertia G, θ σ = 1 ↔ ∀ x : B, (σ : G) • x - x ∈ 𝔓 ^ 2) ∧ IsCyclic θ.range := by p2m_exact_reverting @_root_.P2MW.S_Ideal_exists_monoidHom_inertia_residueFieldUnits_ker_iff_of_uniformizer.solution
