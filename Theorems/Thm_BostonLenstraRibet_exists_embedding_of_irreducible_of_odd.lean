import Mathlib
import P2M.Util
import P2M.Sol.S_BostonLenstraRibet_exists_embedding_of_irreducible_of_odd

theorem BostonLenstraRibet.exists_embedding_of_irreducible_of_odd {k : Type*} [Field k] {G : Type*} [Group G]
    {V : Type*} [AddCommGroup V] [Module k V]
    {ρV : Representation k G V} {ρ : G → Matrix (Fin 2) (Fin 2) k}
    (hρ : ∀ σ τ : G, ρ (σ * τ) = ρ σ * ρ τ)
    (hCH : ∀ σ : G, ρV σ * ρV σ - (ρ σ).trace • ρV σ
      + (ρ σ).det • (1 : Module.End k V) = 0)
    (hirr : ∀ W : Submodule k (Fin 2 → k),
      (∀ g, ∀ v ∈ W, (ρ g).mulVec v ∈ W) → W = ⊥ ∨ W = ⊤)
    {c : G} (hc2 : ρ c * ρ c = 1) (hcdet : (ρ c).det = -1) (h2 : (2 : k) ≠ 0)
    (hV : ∃ v : V, v ≠ 0) :
    ∃ φ : (Fin 2 → k) →ₗ[k] V, Function.Injective φ ∧
      ∀ (σ : G) (v : Fin 2 → k), φ ((ρ σ).mulVec v) = ρV σ (φ v) := by p2m_exact_reverting @_root_.P2MW.S_BostonLenstraRibet_exists_embedding_of_irreducible_of_odd.solution
