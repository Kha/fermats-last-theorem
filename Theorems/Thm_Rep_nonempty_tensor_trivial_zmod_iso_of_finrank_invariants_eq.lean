import Mathlib
import P2M.Util
import P2M.Sol.S_Rep_nonempty_tensor_trivial_zmod_iso_of_finrank_invariants_eq

set_option autoImplicit false

open CategoryTheory MonoidalCategory Module
open scoped Classical

theorem Rep.nonempty_tensor_trivial_zmod_iso_of_finrank_invariants_eq
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] (hG : (Nat.card G).Coprime p)
    (L L' : Rep.{0} ℤ G) [Module.Finite ℤ L] [Module.Free ℤ L] [Module.Finite ℤ L'] [Module.Free ℤ L']
    (h : ∀ H : Subgroup G, Module.finrank ℤ (groupCohomology (Rep.res H.subtype L) 0) =
      Module.finrank ℤ (groupCohomology (Rep.res H.subtype L') 0)) :
    Nonempty (L ⊗ Rep.trivial ℤ G (ZMod p) ≅ L' ⊗ Rep.trivial ℤ G (ZMod p)) := by p2m_exact_reverting @_root_.P2MW.S_Rep_nonempty_tensor_trivial_zmod_iso_of_finrank_invariants_eq.solution
