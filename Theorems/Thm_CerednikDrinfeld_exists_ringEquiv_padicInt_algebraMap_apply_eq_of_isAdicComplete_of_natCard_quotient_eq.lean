import Mathlib
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_exists_ringEquiv_padicInt_algebraMap_apply_eq_of_isAdicComplete_of_natCard_quotient_eq

set_option autoImplicit false

theorem CerednikDrinfeld.exists_ringEquiv_padicInt_algebraMap_apply_eq_of_isAdicComplete_of_natCard_quotient_eq
    (r : ℕ) [Fact r.Prime]
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [CharZero 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
    (π : 𝒪) (hπ : Irreducible π) (hcomplete : IsAdicComplete (Ideal.span {π}) 𝒪)
    (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r) (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π})
    (K₀ : Type) [Field K₀] [CharZero K₀] [Algebra 𝒪 K₀] [IsFractionRing 𝒪 K₀] :
    ∃ (e𝒪 : ℤ_[r] ≃+* 𝒪) (eK : ℚ_[r] ≃+* K₀),
      ∀ x : ℤ_[r], algebraMap 𝒪 K₀ (e𝒪 x) = eK (x : ℚ_[r]) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_exists_ringEquiv_padicInt_algebraMap_apply_eq_of_isAdicComplete_of_natCard_quotient_eq.solution
