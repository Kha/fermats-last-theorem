import Mathlib
import P2M.Util
import P2M.Sol.S_Representation_exists_submodule_quotient_line_of_commutator_le_of_isPGroup

set_option autoImplicit false

universe u v

theorem Representation.exists_submodule_quotient_line_of_commutator_le_of_isPGroup
    (p : ℕ) [Fact p.Prime]
    {Γ : Type u} [Group Γ] [Finite Γ] (P : Subgroup Γ) [P.Normal] (hP : IsPGroup p ↥P)
    (hcomm : ∀ a b : Γ, a⁻¹ * b⁻¹ * a * b ∈ P)
    {V : Type v} [AddCommGroup V] [Module (ZMod p) V] [Finite V] [Nontrivial V]
    (ρ : Representation (ZMod p) Γ V) :
    ∃ W : Submodule (ZMod p) V, (∀ (g : Γ) (v : V), v ∈ W → ρ g v ∈ W) ∧ W ≠ ⊤ ∧
      ∃ (F : Type) (_ : Field F) (_ : Fintype F) (_ : Module F (V ⧸ W)) (r : ℕ),
        0 < r ∧ Fintype.card F = p ^ r ∧
        (∀ (m : ℕ) (q : V ⧸ W), (m : F) • q = m • q) ∧
        Module.finrank F (V ⧸ W) = 1 ∧
        (∀ g : Γ, ∃ a : F, ∀ v : V, W.mkQ (ρ g v) = a • W.mkQ v) := by p2m_exact_reverting @_root_.P2MW.S_Representation_exists_submodule_quotient_line_of_commutator_le_of_isPGroup.solution
