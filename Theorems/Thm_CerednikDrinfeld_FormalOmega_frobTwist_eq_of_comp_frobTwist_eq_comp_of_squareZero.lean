import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalOmega_frobTwist_eq_of_comp_frobTwist_eq_comp_of_squareZero

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.FormalOmega.frobTwist_eq_of_comp_frobTwist_eq_comp_of_squareZero
    {𝒪 : Type} [CommRing 𝒪] (π : 𝒪) (r : ℕ) [Fact r.Prime]
    (Onr : Type) [CommRing Onr] [Algebra 𝒪 Onr] (Fr : Onr ≃ₐ[𝒪] Onr)
    (hOnr_closed : ∀ q : Polynomial Onr, q.Monic → 0 < q.natDegree → ∃ x : Onr, Polynomial.eval x q ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (hFr : ∀ x : Onr, Fr x - x ^ r ∈ Ideal.span {algebraMap 𝒪 Onr π})
    {B B₀ : Type} [CommRing B] [Algebra 𝒪 B] [CommRing B₀] [Algebra 𝒪 B₀]
    (hB₀ : IsNilpotent (algebraMap 𝒪 B₀ π))
    (p : B →ₐ[𝒪] B₀) (hp2 : ∀ s t : B, p s = 0 → p t = 0 → s * t = 0)
    (χ : Onr →ₐ[𝒪] B) (k : ℤ)
    (h : p.comp (frobTwist Onr Fr k χ) = p.comp χ) :
    frobTwist Onr Fr k χ = χ := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalOmega_frobTwist_eq_of_comp_frobTwist_eq_comp_of_squareZero.solution
