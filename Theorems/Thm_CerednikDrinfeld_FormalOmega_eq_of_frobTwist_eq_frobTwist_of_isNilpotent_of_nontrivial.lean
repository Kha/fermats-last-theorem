import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalOmega_eq_of_frobTwist_eq_frobTwist_of_isNilpotent_of_nontrivial

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.FormalOmega.eq_of_frobTwist_eq_frobTwist_of_isNilpotent_of_nontrivial
    {𝒪 : Type} [CommRing 𝒪] (π : 𝒪) {r : ℕ} [Fact r.Prime]
    (Onr : Type) [CommRing Onr] [Nontrivial Onr] [Algebra 𝒪 Onr] (Fr : Onr ≃ₐ[𝒪] Onr)
    (hOnr_closed : ∀ p : Polynomial Onr, p.Monic → 0 < p.natDegree →
      ∃ x : Onr, Polynomial.eval x p ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (hFr : ∀ x : Onr, Fr x - x ^ r ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (B : Type) [CommRing B] [Algebra 𝒪 B] [Nontrivial B] (hB : IsNilpotent (algebraMap 𝒪 B π))
    (ψ : Onr →ₐ[𝒪] B) (a b : ℤ) (h : frobTwist Onr Fr a ψ = frobTwist Onr Fr b ψ) : a = b := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalOmega_eq_of_frobTwist_eq_frobTwist_of_isNilpotent_of_nontrivial.solution
