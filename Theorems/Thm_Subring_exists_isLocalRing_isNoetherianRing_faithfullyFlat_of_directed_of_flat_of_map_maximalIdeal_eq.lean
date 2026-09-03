import Mathlib
import P2M.Util
import P2M.Sol.S_Subring_exists_isLocalRing_isNoetherianRing_faithfullyFlat_of_directed_of_flat_of_map_maximalIdeal_eq

set_option autoImplicit false

universe u v

open IsLocalRing

theorem Subring.exists_isLocalRing_isNoetherianRing_faithfullyFlat_of_directed_of_flat_of_map_maximalIdeal_eq
    (A : Type u) [CommRing A] {ι : Type v} [Preorder ι] [Nonempty ι] [IsDirected ι (· ≤ ·)]
    (S : ι → Subring A) (hS : Monotone S) (hcov : ∀ x : A, ∃ i, x ∈ S i)
    [∀ i, IsLocalRing (S i)] [∀ i, IsNoetherianRing (S i)]
    (hflat : ∀ ⦃i j : ι⦄ (h : i ≤ j), (Subring.inclusion (hS h)).Flat)
    (hmax : ∀ ⦃i j : ι⦄ (h : i ≤ j),
      Ideal.map (Subring.inclusion (hS h)) (maximalIdeal (S i)) = maximalIdeal (S j)) :
    ∃ _ : IsLocalRing A, IsNoetherianRing A ∧
      ∀ i, Module.FaithfullyFlat (S i) A ∧
        Ideal.map (algebraMap (S i) A) (maximalIdeal (S i)) = maximalIdeal A := by p2m_exact_reverting @_root_.P2MW.S_Subring_exists_isLocalRing_isNoetherianRing_faithfullyFlat_of_directed_of_flat_of_map_maximalIdeal_eq.solution
