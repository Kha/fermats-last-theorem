import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_Omega_RatPair_identityPrinciple_disc

set_option autoImplicit false

open CerednikDrinfeld.Omega

theorem CerednikDrinfeld.Omega.RatPair.identityPrinciple_disc
    (K : Type) [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [IsAlgClosed K]
    (S : Set K) (r : ℕ → RatPair K) (hr : ∀ k, (r k).IsPoleFreeOn S)
    (c π : K) (hπ : π ≠ 0) (Z : Finset K) (hZ : ∀ ζ ∈ Z, Valued.v π ≤ Valued.v (c - ζ))
    (hS : ∀ z : K, Valued.v (z - c) ≤ Valued.v π → (∀ ζ ∈ Z, Valued.v π ≤ Valued.v (z - ζ)) → z ∈ S)
    (hC : ∀ e : K, e ≠ 0 → ∃ N : ℕ, ∀ k ≥ N, ∀ j ≥ N, ∀ z ∈ S,
      Valued.v ((r k).evalAt z - (r j).evalAt z) < Valued.v e)
    (δ : K) (hδ : δ ≠ 0)
    (h0 : ∀ e : K, e ≠ 0 → ∃ N : ℕ, ∀ k ≥ N, ∀ z ∈ S, Valued.v (z - c) ≤ Valued.v δ →
      Valued.v ((r k).evalAt z) < Valued.v e) :
    ∀ e : K, e ≠ 0 → ∃ N : ℕ, ∀ k ≥ N, ∀ z : K, Valued.v (z - c) ≤ Valued.v π →
      (∀ ζ ∈ Z, Valued.v π ≤ Valued.v (z - ζ)) → Valued.v ((r k).evalAt z) < Valued.v e := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_Omega_RatPair_identityPrinciple_disc.solution
