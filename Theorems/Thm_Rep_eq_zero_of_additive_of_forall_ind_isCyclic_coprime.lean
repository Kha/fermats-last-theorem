import Mathlib
import P2M.Util
import P2M.Sol.S_Rep_eq_zero_of_additive_of_forall_ind_isCyclic_coprime

set_option autoImplicit false
open CategoryTheory
theorem Rep.eq_zero_of_additive_of_forall_ind_isCyclic_coprime
    {p : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]
    (ψ : Rep.{0} (ZMod p) G → ℤ)
    (hadd : ∀ (X : ShortComplex (Rep.{0} (ZMod p) G)), X.ShortExact →
      FiniteDimensional (ZMod p) X.X₂ → ψ X.X₂ = ψ X.X₁ + ψ X.X₃)
    (hind : ∀ (H : Subgroup G), IsCyclic H → (Nat.card H).Coprime p →
      ∀ (N : Rep.{0} (ZMod p) ↥H), FiniteDimensional (ZMod p) N → ψ (Rep.ind H.subtype N) = 0)
    (M : Rep.{0} (ZMod p) G) [FiniteDimensional (ZMod p) M] :
    ψ M = 0 := by p2m_exact_reverting @_root_.P2MW.S_Rep_eq_zero_of_additive_of_forall_ind_isCyclic_coprime.solution
