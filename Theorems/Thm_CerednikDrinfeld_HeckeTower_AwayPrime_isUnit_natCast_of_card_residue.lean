import Definitions.Def_CerednikDrinfeld_HeckeTower
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_HeckeTower_AwayPrime_isUnit_natCast_of_card_residue

set_option autoImplicit false

open CerednikDrinfeld

theorem CerednikDrinfeld.HeckeTower.AwayPrime.isUnit_natCast_of_card_residue
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime]
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
    (π : 𝒪) (hπ : Irreducible π) (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = q)
    (ℓ : HeckeTower.AwayPrime q q') :
    IsUnit (((ℓ.1 : ℕ) : ℕ) : 𝒪) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_HeckeTower_AwayPrime_isUnit_natCast_of_card_residue.solution
