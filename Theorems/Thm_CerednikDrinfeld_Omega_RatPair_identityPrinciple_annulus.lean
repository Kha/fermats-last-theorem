import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_Omega_RatPair_identityPrinciple_annulus

set_option autoImplicit false

open CerednikDrinfeld.Omega

theorem CerednikDrinfeld.Omega.RatPair.identityPrinciple_annulus
    (K : Type) [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [IsAlgClosed K]
    (S : Set K) (r : ℕ → RatPair K) (hr : ∀ k, (r k).IsPoleFreeOn S)
    (c πd πs : K) (hπd : πd ≠ 0) (hπs : πs ≠ 0) (hlt : Valued.v πs < Valued.v πd)
    (Z : Finset K) (hZ : ∀ ζ ∈ Z, Valued.v πd ≤ Valued.v (c - ζ))
    (Ξ : Finset K) (hΞ : ∀ ξ ∈ Ξ, Valued.v (c - ξ) ≤ Valued.v πs)
    (hS : ∀ z : K, Valued.v πs ≤ Valued.v (z - c) → Valued.v (z - c) ≤ Valued.v πd →
      (∀ ζ ∈ Z, Valued.v πd ≤ Valued.v (z - ζ)) → (∀ ξ ∈ Ξ, Valued.v πs ≤ Valued.v (z - ξ)) → z ∈ S)
    (hC : ∀ e : K, e ≠ 0 → ∃ N : ℕ, ∀ k ≥ N, ∀ j ≥ N, ∀ z ∈ S,
      Valued.v ((r k).evalAt z - (r j).evalAt z) < Valued.v e)
    (h0 : (∀ e : K, e ≠ 0 → ∃ N : ℕ, ∀ k ≥ N, ∀ z : K, Valued.v (z - c) = Valued.v πd →
            (∀ ζ ∈ Z, Valued.v πd ≤ Valued.v (z - ζ)) → Valued.v ((r k).evalAt z) < Valued.v e) ∨
          (∀ e : K, e ≠ 0 → ∃ N : ℕ, ∀ k ≥ N, ∀ z : K, Valued.v (z - c) = Valued.v πs →
            (∀ ξ ∈ Ξ, Valued.v πs ≤ Valued.v (z - ξ)) → Valued.v ((r k).evalAt z) < Valued.v e)) :
    ∀ e : K, e ≠ 0 → ∃ N : ℕ, ∀ k ≥ N, ∀ z : K, Valued.v πs ≤ Valued.v (z - c) → Valued.v (z - c) ≤ Valued.v πd →
      (∀ ζ ∈ Z, Valued.v πd ≤ Valued.v (z - ζ)) → (∀ ξ ∈ Ξ, Valued.v πs ≤ Valued.v (z - ξ)) →
      Valued.v ((r k).evalAt z) < Valued.v e := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_Omega_RatPair_identityPrinciple_annulus.solution
