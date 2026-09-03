import Mathlib
import Definitions.Def_PDivisibleGroup_Basic
import P2M.Util
import P2M.Sol.S_PDivisibleGroup_finrank_cotangent_augIdeal_eq_of_isLocalRing

universe v

theorem PDivisibleGroup.finrank_cotangent_augIdeal_eq_of_isLocalRing
    (p : ℕ) [Fact p.Prime] (h₀ : ℕ)
    (H : ℕ → Type v) [∀ v, CommRing (H v)] [∀ v, HopfAlgebra (ZMod p) (H v)]
    [∀ v, Coalgebra.IsCocomm (ZMod p) (H v)] [∀ v, Module.Finite (ZMod p) (H v)]
    (s : ∀ v, H (v + 1) →ₐc[ZMod p] H v) (hs : ∀ v, Function.Surjective (s v))
    (hrankH : ∀ v, Module.finrank (ZMod p) (H v) = p ^ (v * h₀))
    (hkerH : ∀ v, RingHom.ker (s v) = PDivisibleGroup.Hopf.torsionIdeal (ZMod p) (H (v + 1)) (p ^ v))
    (hlocH : ∀ v, IsLocalRing (H v))
    (w : ℕ) (hw : 1 ≤ w) :
    Module.finrank (ZMod p) (PDivisibleGroup.Hopf.augIdeal (ZMod p) (H w)).Cotangent =
      Module.finrank (ZMod p) (PDivisibleGroup.Hopf.augIdeal (ZMod p) (H 1)).Cotangent := by p2m_exact_reverting @_root_.P2MW.S_PDivisibleGroup_finrank_cotangent_augIdeal_eq_of_isLocalRing.solution
