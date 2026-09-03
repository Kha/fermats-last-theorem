import Mathlib
import P2M.Util
import P2M.Sol.S_Rep_exists_isIrreducible_trace_eq_sum_of_card_coprime

set_option autoImplicit false

open CategoryTheory MonoidalCategory Module
open scoped Classical

theorem Rep.exists_isIrreducible_trace_eq_sum_of_card_coprime
    {p : ℕ} [Fact p.Prime] {H : Type} [Group H] [Finite H] (hH : (Nat.card H).Coprime p) :
    ∃ (s : ℕ) (T : Fin s → Rep.{0} (ZMod p) H),
      (∀ j, FiniteDimensional (ZMod p) (T j) ∧ (T j).ρ.IsIrreducible) ∧
      (∀ i j, Nonempty (T i ≅ T j) → i = j) ∧
      ∀ (V : Rep.{0} (ZMod p) H), FiniteDimensional (ZMod p) V →
        ∃ m : Fin s → ℕ, (∀ j, Module.finrank (ZMod p) (T j ⟶ V) = m j * Module.finrank (ZMod p) (T j ⟶ T j)) ∧
          ∀ h : H, LinearMap.trace (ZMod p) V (V.ρ h) =
            ∑ j, (m j : ZMod p) * LinearMap.trace (ZMod p) (T j) ((T j).ρ h) := by p2m_exact_reverting @_root_.P2MW.S_Rep_exists_isIrreducible_trace_eq_sum_of_card_coprime.solution
