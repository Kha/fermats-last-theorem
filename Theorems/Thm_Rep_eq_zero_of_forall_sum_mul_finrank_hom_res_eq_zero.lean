import Mathlib
import P2M.Util
import P2M.Sol.S_Rep_eq_zero_of_forall_sum_mul_finrank_hom_res_eq_zero

set_option autoImplicit false

open CategoryTheory MonoidalCategory Module
open scoped Classical

theorem Rep.eq_zero_of_forall_sum_mul_finrank_hom_res_eq_zero
    {p : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]
    {r : ℕ} (S : Fin r → Rep.{0} (ZMod p) G) [∀ i, FiniteDimensional (ZMod p) (S i)]
    (hS : ∀ i, (S i).ρ.IsIrreducible) (hij : ∀ i j, Nonempty (S i ≅ S j) → i = j)
    (n : Fin r → ℤ)
    (h : ∀ H : Subgroup G, IsCyclic H → (Nat.card H).Coprime p →
      ∀ T : Rep.{0} (ZMod p) H, FiniteDimensional (ZMod p) T →
        ∑ i, n i * (Module.finrank (ZMod p) (T ⟶ Rep.res H.subtype (S i)) : ℤ) = 0) :
    n = 0 := by p2m_exact_reverting @_root_.P2MW.S_Rep_eq_zero_of_forall_sum_mul_finrank_hom_res_eq_zero.solution
