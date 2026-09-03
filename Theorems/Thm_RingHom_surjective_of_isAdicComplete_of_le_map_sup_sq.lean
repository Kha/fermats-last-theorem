import Mathlib
import P2M.Util
import P2M.Sol.S_RingHom_surjective_of_isAdicComplete_of_le_map_sup_sq

set_option autoImplicit false

universe u

open IsLocalRing

theorem RingHom.surjective_of_isAdicComplete_of_le_map_sup_sq
    {P R : Type u} [CommRing P] [CommRing R] (J : Ideal P) [IsAdicComplete J P] (I : Ideal R) [IsHausdorff I R]
    (φ : P →+* R) (hJ : Ideal.map φ J ≤ I)
    (h0 : ∀ r : R, ∃ p : P, r - φ p ∈ I)
    (h1 : I ≤ Ideal.map φ J ⊔ I ^ 2) :
    Function.Surjective φ := by p2m_exact_reverting @_root_.P2MW.S_RingHom_surjective_of_isAdicComplete_of_le_map_sup_sq.solution
