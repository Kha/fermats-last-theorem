import Mathlib
import P2M.Util
import P2M.Sol.S_Representation_nonempty_equiv_torsionBy_quotient_of_coprime

set_option autoImplicit false

open CategoryTheory MonoidalCategory Module
open scoped Classical TensorProduct Pointwise

theorem Representation.nonempty_equiv_torsionBy_quotient_of_coprime
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] (hG : (Nat.card G).Coprime p)
    {A : Type} [AddCommGroup A] [Finite A] (ρ : Representation ℤ G A)
    (h1 : ∀ g, Submodule.torsionBy ℤ A (p : ℤ) ≤ (Submodule.torsionBy ℤ A (p : ℤ)).comap (ρ g))
    (h2 : ∀ g, (p : ℤ) • (⊤ : Submodule ℤ A) ≤ ((p : ℤ) • (⊤ : Submodule ℤ A)).comap (ρ g)) :
    Nonempty ((ρ.subrepresentation _ h1).Equiv (ρ.quotient _ h2)) := by p2m_exact_reverting @_root_.P2MW.S_Representation_nonempty_equiv_torsionBy_quotient_of_coprime.solution
