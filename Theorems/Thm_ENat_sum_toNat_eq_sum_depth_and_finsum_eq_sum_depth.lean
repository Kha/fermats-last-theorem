import Mathlib
import P2M.Util
import P2M.Sol.S_ENat_sum_toNat_eq_sum_depth_and_finsum_eq_sum_depth
set_option autoImplicit false

theorem ENat.sum_toNat_eq_sum_depth_and_finsum_eq_sum_depth
    {Pl Pr : Type*} (E r : ℕ)
    (Ttot : Finset Pl) (ordZ : Pl → ℤ)
    (dep : Pl → ℕ) (hdep : ∀ V ∈ Ttot, 1 ≤ dep V ∧ dep V + 1 ≤ r * E)
    (T : ℕ → Finset Pl) (hT : ∀ p V, V ∈ T p ↔ V ∈ Ttot ∧ dep V = p)
    (horiz : Pr → Prop) (rk : Pr → ℕ) (lenU mult : Pr → ℕ∞) (depQ : Pr → ℕ)
    (hdepQ : ∀ Q, horiz Q → mult Q ≠ 0 →
      1 ≤ depQ Q ∧ depQ Q + 1 ≤ r * E ∧ (r : ℕ∞) * lenU Q = ((depQ Q * rk Q : ℕ) : ℕ∞) ∧
        1 ≤ rk Q ∧ lenU Q ≠ ⊤)
    (hfin : {Q : Pr | horiz Q ∧ mult Q ≠ 0}.Finite) :
    ((∑ V ∈ Ttot, (ordZ V).toNat : ℕ) : ℕ∞) =
        ∑ p ∈ Finset.Icc 1 (r * E - 1), ((∑ V ∈ T p, (ordZ V).toNat : ℕ) : ℕ∞) ∧
    (∑ᶠ (Q : Pr) (_ : horiz Q), (rk Q : ℕ∞) * mult Q) =
        ∑ p ∈ Finset.Icc 1 (r * E - 1),
          ∑ᶠ (Q : Pr) (_ : horiz Q ∧ (r : ℕ∞) * lenU Q = ((p * rk Q : ℕ) : ℕ∞)), (rk Q : ℕ∞) * mult Q := by p2m_exact_reverting @_root_.P2MW.S_ENat_sum_toNat_eq_sum_depth_and_finsum_eq_sum_depth.solution
