import Mathlib
import P2M.Util
import P2M.Sol.S_Submodule_not_exists_cofixed_line_of_inertia_and_branch_swap

theorem Submodule.not_exists_cofixed_line_of_inertia_and_branch_swap
    {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    {V : Type*} [AddCommGroup V] [Module (ZMod p) V] (hcard : Nat.card V = p ^ 2)
    {G : Type*} [SMul G V] {I : Set G} {M : Submodule (ZMod p) V}
    (hMtop : M ≠ ⊤)
    (hIquo : ∀ τ ∈ I, ∀ y : V, τ • y - y ∈ M)
    (hIram : ∃ τ ∈ I, ∃ y : V, τ • y ≠ y)
    (hswap : ∃ σ : G, ∀ y : V, y ∉ M → σ • y + y ∈ M) :
    ¬ ∃ N : Submodule (ZMod p) V,
        (∀ g : G, ∀ x ∈ N, g • x ∈ N) ∧ N ≠ ⊥ ∧ N ≠ ⊤ ∧
          ∀ g : G, ∀ y : V, g • y - y ∈ N := by p2m_exact_reverting @_root_.P2MW.S_Submodule_not_exists_cofixed_line_of_inertia_and_branch_swap.solution
