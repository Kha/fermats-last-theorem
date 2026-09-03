import Mathlib
import P2M.Util
import P2M.Sol.S_Int_natCast_dvd_of_forall_frobeniusLift_pow_fixed_apply_zpow_eq

set_option autoImplicit false

theorem Int.natCast_dvd_of_forall_frobeniusLift_pow_fixed_apply_zpow_eq
    {r : ℕ} [Fact r.Prime]
    {𝒪 : Type} [CommRing 𝒪] (π : 𝒪)
    (Onr : Type) [CommRing Onr] [IsDomain Onr] [Algebra 𝒪 Onr] (Fr : Onr ≃ₐ[𝒪] Onr)
    (hOnr_complete : IsAdicComplete (Ideal.span {algebraMap 𝒪 Onr π}) Onr)
    (hOnr_max : (Ideal.span {algebraMap 𝒪 Onr π}).IsMaximal)
    (hOnr_closed : ∀ p : Polynomial Onr, p.Monic → 0 < p.natDegree → ∃ x : Onr, Polynomial.eval x p ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (hFr : ∀ x : Onr, Fr x - x ^ r ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (hr : ((r : ℕ) : Onr) ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (k : Type) [Field k] (ψ : Onr →+* k) (hψ : ψ (algebraMap 𝒪 Onr π) = 0)
    (d : ℕ) (hd : 0 < d) (v : ℤ)
    (h : ∀ y : Onr, (Fr ^ (d : ℤ)) y = y → ψ ((Fr ^ (-v)) y) = ψ y) :
    (d : ℤ) ∣ v := by p2m_exact_reverting @_root_.P2MW.S_Int_natCast_dvd_of_forall_frobeniusLift_pow_fixed_apply_zpow_eq.solution
