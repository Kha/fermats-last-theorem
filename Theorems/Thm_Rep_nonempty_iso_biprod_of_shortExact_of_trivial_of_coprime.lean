import Mathlib
import P2M.Util
import P2M.Sol.S_Rep_nonempty_iso_biprod_of_shortExact_of_trivial_of_coprime

set_option autoImplicit false

open CategoryTheory MonoidalCategory Module Limits
open scoped Classical

theorem Rep.nonempty_iso_biprod_of_shortExact_of_trivial_of_coprime
    {p : ℕ} [Fact p.Prime] {Γ : Type} [Group Γ] (Λ : Subgroup Γ) [Λ.Normal] [Finite (Γ ⧸ Λ)]
    (hcop : (Nat.card (Γ ⧸ Λ)).Coprime p)
    (X : ShortComplex (Rep.{0} (ZMod p) Γ)) (hX : X.ShortExact) [FiniteDimensional (ZMod p) X.X₂]
    (h₂ : ∀ s ∈ Λ, X.X₂.ρ s = 1) :
    Nonempty (X.X₂ ≅ X.X₁ ⊞ X.X₃) := by p2m_exact_reverting @_root_.P2MW.S_Rep_nonempty_iso_biprod_of_shortExact_of_trivial_of_coprime.solution
