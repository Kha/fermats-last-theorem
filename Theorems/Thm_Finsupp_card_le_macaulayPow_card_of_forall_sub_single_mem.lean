import Mathlib
import Definitions.Def_Nat_MacaulayPow
import P2M.Util
import P2M.Sol.S_Finsupp_card_le_macaulayPow_card_of_forall_sub_single_mem

set_option autoImplicit false

theorem Finsupp.card_le_macaulayPow_card_of_forall_sub_single_mem
    (n d : ℕ) (hd : 1 ≤ d) (B : Finset (Fin (n + 1) →₀ ℕ)) (hB : ∀ m ∈ B, m.degree = d)
    (C : Finset (Fin (n + 1) →₀ ℕ)) (hC : ∀ u ∈ C, u.degree = d + 1)
    (hCB : ∀ u ∈ C, ∀ i : Fin (n + 1), 1 ≤ u i → u - Finsupp.single i 1 ∈ B) :
    C.card ≤ Nat.macaulayPow d B.card := by p2m_exact_reverting @_root_.P2MW.S_Finsupp_card_le_macaulayPow_card_of_forall_sub_single_mem.solution
