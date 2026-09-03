import Mathlib
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_exists_forall_apply_eq_apply_frobenius_zpow_of_fixed

set_option autoImplicit false

theorem CerednikDrinfeld.exists_forall_apply_eq_apply_frobenius_zpow_of_fixed
    {r : ℕ} [Fact r.Prime]
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [CharZero 𝒪] (π : 𝒪) (hπ : Irreducible π)
    (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r) (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π})
    (Onr : Type) [CommRing Onr] [IsDomain Onr] [CharZero Onr] [Algebra 𝒪 Onr] (Fr : Onr ≃ₐ[𝒪] Onr)
    (hOnr_complete : IsAdicComplete (Ideal.span {algebraMap 𝒪 Onr π}) Onr)
    (hOnr_max : (Ideal.span {algebraMap 𝒪 Onr π}).IsMaximal)
    (hOnr_alg : ∀ x : Onr, ∃ p : Polynomial 𝒪, p.Monic ∧ Polynomial.aeval x p ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (hOnr_closed : ∀ p : Polynomial Onr, p.Monic → 0 < p.natDegree → ∃ x : Onr, Polynomial.eval x p ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (hFr : ∀ x : Onr, Fr x - x ^ r ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (k : Type) [Field k] [Algebra 𝒪 k] (hk : IsNilpotent (algebraMap 𝒪 k π))
    (ψ ψ' : Onr →ₐ[𝒪] k) (d : ℤ) (hd : d ≠ 0) :
    ∃ j : ℤ, ∀ y : Onr, (Fr ^ d) y = y → ψ' y = ψ ((Fr ^ j) y) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_exists_forall_apply_eq_apply_frobenius_zpow_of_fixed.solution
