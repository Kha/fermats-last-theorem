import Mathlib
import P2M.Util
import P2M.Sol.S_Representation_norm_eq_zero_of_dvd_card

open CategoryTheory
theorem Representation.norm_eq_zero_of_dvd_card {k Q V : Type*} [Field k] [Group Q] [Fintype Q] [AddCommGroup V] [Module k V] (ρ : Representation k Q V)
    (p : ℕ) [CharP k p] {g : Q} (hg : ∀ x : Q, x ∈ Subgroup.zpowers g) {d : ℕ} (hd : ρ g ^ d = 1) (hpd : p * d ∣ Fintype.card Q) :
    ρ.norm = 0 := by p2m_exact_reverting @_root_.P2MW.S_Representation_norm_eq_zero_of_dvd_card.solution
