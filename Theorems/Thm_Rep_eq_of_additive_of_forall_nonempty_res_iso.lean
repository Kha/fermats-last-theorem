import Mathlib
import P2M.Util
import P2M.Sol.S_Rep_eq_of_additive_of_forall_nonempty_res_iso

set_option autoImplicit false

open CategoryTheory MonoidalCategory Module
open scoped Classical

theorem Rep.eq_of_additive_of_forall_nonempty_res_iso
    {p : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]
    (ψ : Rep.{0} (ZMod p) G → ℤ)
    (hadd : ∀ (X : ShortComplex (Rep.{0} (ZMod p) G)), X.ShortExact →
      FiniteDimensional (ZMod p) X.X₂ → ψ X.X₂ = ψ X.X₁ + ψ X.X₃)
    (A B : Rep.{0} (ZMod p) G) [FiniteDimensional (ZMod p) A] [FiniteDimensional (ZMod p) B]
    (h : ∀ H : Subgroup G, IsCyclic H → (Nat.card H).Coprime p →
      Nonempty (Rep.res H.subtype A ≅ Rep.res H.subtype B)) :
    ψ A = ψ B := by p2m_exact_reverting @_root_.P2MW.S_Rep_eq_of_additive_of_forall_nonempty_res_iso.solution
