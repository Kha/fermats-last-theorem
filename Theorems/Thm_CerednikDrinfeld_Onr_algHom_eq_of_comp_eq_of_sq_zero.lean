import Mathlib
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_Onr_algHom_eq_of_comp_eq_of_sq_zero

set_option autoImplicit false

theorem CerednikDrinfeld.Onr.algHom_eq_of_comp_eq_of_sq_zero
    {r : ℕ} [Fact r.Prime]
    (𝒪 : Type) [CommRing 𝒪] (π : 𝒪)
    (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r) (hunr : ((r : ℕ) : 𝒪) ∈ Ideal.span {π})
    (Onr : Type) [CommRing Onr] [Algebra 𝒪 Onr]
    (hOnr_prime : (Ideal.span {algebraMap 𝒪 Onr π}).IsPrime)
    (hOnr_alg : ∀ x : Onr, ∃ p : Polynomial 𝒪, p.Monic ∧ Polynomial.aeval x p ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (C C₀ : Type) [CommRing C] [CommRing C₀] [Algebra 𝒪 C] [Algebra 𝒪 C₀] (hC : IsNilpotent (algebraMap 𝒪 C π))
    (p : C →ₐ[𝒪] C₀) (hsq : ∀ s t : C, p s = 0 → p t = 0 → s * t = 0)
    (ψ ψ' : Onr →ₐ[𝒪] C) (h : p.comp ψ = p.comp ψ') :
    ψ = ψ' := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_Onr_algHom_eq_of_comp_eq_of_sq_zero.solution
