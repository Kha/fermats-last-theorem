import Mathlib
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_isUnit_natCast_of_not_dvd_of_card_quotient

set_option autoImplicit false

theorem CerednikDrinfeld.isUnit_natCast_of_not_dvd_of_card_quotient
    {r : ℕ} [Fact r.Prime]
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪]
    (π : 𝒪) (hcomplete : IsAdicComplete (Ideal.span {π}) 𝒪)
    (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r) (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π})
    (m : ℕ) (hm : ¬ r ∣ m) :
    IsUnit ((m : ℕ) : 𝒪) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_isUnit_natCast_of_not_dvd_of_card_quotient.solution
