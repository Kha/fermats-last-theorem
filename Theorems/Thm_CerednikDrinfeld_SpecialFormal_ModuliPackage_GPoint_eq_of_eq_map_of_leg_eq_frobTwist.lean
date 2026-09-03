import Definitions.Def_CerednikDrinfeld_SpecialFormalFunctorG
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_SpecialFormal_ModuliPackage_GPoint_eq_of_eq_map_of_leg_eq_frobTwist

set_option autoImplicit false

p2m_open "CerednikDrinfeld CerednikDrinfeld.FormalOmega~eq_of_frobTwist_eq_frobTwist_of_isNilpotent_of_nontrivial CerednikDrinfeld.SpecialFormal"

theorem CerednikDrinfeld.SpecialFormal.ModuliPackage.GPoint.eq_of_eq_map_of_leg_eq_frobTwist
    {𝒪 : Type} [CommRing 𝒪] (π : 𝒪) {r : ℕ} [Fact r.Prime]
    (Onr : Type) [CommRing Onr] [Nontrivial Onr] [Algebra 𝒪 Onr] (Fr : Onr ≃ₐ[𝒪] Onr)
    (hOnr_closed : ∀ p : Polynomial Onr, p.Monic → 0 < p.natDegree →
      ∃ x : Onr, Polynomial.eval x p ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (hFr : ∀ x : Onr, Fr x - x ^ r ∈ Ideal.span {algebraMap 𝒪 Onr π})
    {M : ModuliPackage.{0, 0} r Onr}
    {B L : Type} [CommRing B] [Algebra 𝒪 B] [CommRing L] [Algebra 𝒪 L] [Nontrivial L]
    (ψ : Onr →ₐ[𝒪] B) (φ : B →ₐ[𝒪] L) (hL : IsNilpotent (algebraMap 𝒪 L π))
    (xB : ModuliPackage.GPoint 𝒪 M B) (xL : ModuliPackage.GPoint 𝒪 M L) (hnat : xL = xB.map φ)
    (k₀ j : ℤ) (hk₀ : xB.ψ = frobTwist Onr Fr k₀ ψ) (hj : xL.ψ = frobTwist Onr Fr j (φ.comp ψ)) :
    j = k₀ := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_SpecialFormal_ModuliPackage_GPoint_eq_of_eq_map_of_leg_eq_frobTwist.solution
