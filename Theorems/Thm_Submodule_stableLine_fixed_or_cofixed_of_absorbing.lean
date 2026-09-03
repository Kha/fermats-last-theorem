import Mathlib
import P2M.Util
import P2M.Sol.S_Submodule_stableLine_fixed_or_cofixed_of_absorbing

theorem Submodule.stableLine_fixed_or_cofixed_of_absorbing {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V] (hV : Nat.card V = p ^ 2) {G : Type*} [SMul G V] (S : Set G) (N : Submodule (ZMod p) V) (hN : ∀ g ∈ S, ∀ x ∈ N, g • x ∈ N) (hbot : N ≠ ⊥) (htop : N ≠ ⊤) (M : Submodule (ZMod p) V) (hM : M ≠ ⊤) (habs : ∀ g ∈ S, ∀ y : V, g • y - y ∈ M) : (∀ g ∈ S, ∀ x ∈ N, g • x = x) ∨ (∀ g ∈ S, ∀ y : V, g • y - y ∈ N) := by p2m_exact_reverting @_root_.P2MW.S_Submodule_stableLine_fixed_or_cofixed_of_absorbing.solution
