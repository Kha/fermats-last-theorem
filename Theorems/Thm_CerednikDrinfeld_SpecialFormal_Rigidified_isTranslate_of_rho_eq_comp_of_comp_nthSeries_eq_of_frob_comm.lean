import Definitions.Def_CerednikDrinfeld_QMRigidification
import Definitions.Def_CerednikDrinfeld_SpecialFormalFunctorG
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_SpecialFormal_Rigidified_isTranslate_of_rho_eq_comp_of_comp_nthSeries_eq_of_frob_comm

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory AlgebraicGeometry CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.SpecialFormal NeronModelInfra GoodReductionJacobian

theorem CerednikDrinfeld.SpecialFormal.Rigidified.isTranslate_of_rho_eq_comp_of_comp_nthSeries_eq_of_frob_comm
    {r : ℕ} [Fact r.Prime] {𝒪 : Type} [CommRing 𝒪] (π : 𝒪) {Onr : Type} [CommRing Onr] [Algebra 𝒪 Onr]
    (Φ : FormalODModule r (Onr ⧸ pIdeal r Onr)) (X₀ : FormalODModule r (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))
    (κ : (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) →+* (Onr ⧸ pIdeal r Onr))
    (β₀ β₀' : Series (Onr ⧸ pIdeal r Onr)) (N : ℕ)
    (hβ₀ : FormalODModule.IsODHom Φ (X₀.map κ) β₀) (hβ₀' : FormalODModule.IsODHom (X₀.map κ) Φ β₀')
    (h₂ : β₀.comp β₀' = (X₀.map κ).act ((r : Zp2 r) ^ N))
    {B : Type} [CommRing B] [Algebra 𝒪 B] (ψ : Onr →ₐ[𝒪] B) (χ : Onr →+* B)
    (X : FormalODModule r B) (t t' : Rigidified r Φ B) (hXt : t.X = X) (hXt' : t'.X = X)

    (κB : (B ⧸ Ideal.span {algebraMap 𝒪 B π}) →+* (B ⧸ pIdeal r B))
    (hκB₁ : κB.comp (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 B π})) = Ideal.Quotient.mk (pIdeal r B))
    (hκB₂ : κB.comp (FakeEllipticCurve.Rigidification.residueLeg π ψ) = (residueMap (ψ : Onr →+* B)).comp κ)
    (σ σ' : Series (B ⧸ Ideal.span {algebraMap 𝒪 B π}))
    (hσ0 : ∀ i, MvPowerSeries.constantCoeff (σ i) = 0) (hσ'0 : ∀ i, MvPowerSeries.constantCoeff (σ' i) = 0)
    (j j' : ℕ)
    (ht : t.ρ = (Series.map κB σ).comp ((Series.map (residueMap (ψ : Onr →+* B)) β₀).comp (frobSeries (p := r) _ j)))
    (ht' : t'.ρ = (Series.map κB σ').comp ((Series.map (residueMap (ψ : Onr →+* B)) β₀).comp (frobSeries (p := r) _ j')))

    (hσN : (Series.map (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 B π})) (X.F.nthSeries (r ^ N))).comp σ =
      σ.comp (Series.map (FakeEllipticCurve.Rigidification.residueLeg π ψ) (X₀.F.nthSeries (r ^ N))))

    (ε' : Series (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π})) (hε'0 : ∀ i, MvPowerSeries.constantCoeff (ε' i) = 0) (a c : ℕ)
    (hσσ' : (Series.map (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 B π})) (X.F.nthSeries (r ^ a))).comp σ' =
      (Series.map (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 B π})) (X.F.nthSeries (r ^ c))).comp
        (σ.comp (Series.map (FakeEllipticCurve.Rigidification.residueLeg π ψ) ε')))

    (e' : Series (Onr ⧸ pIdeal r Onr)) (he' : e' = β₀'.comp ((Series.map κ ε').comp β₀))
    (hfrob : (frobSeries (p := r) _ j).comp (Series.map (residueMap χ) e') =
      (Series.map (residueMap (ψ : Onr →+* B)) e').comp (frobSeries (p := r) _ j))

    (k m' : ℕ) (hk : t.n + k + c = t'.n + N + a) (hm : j' + m' = j + 2 * k) :
    Rigidified.IsTranslate e' k m' χ t t' := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_isTranslate_of_rho_eq_comp_of_comp_nthSeries_eq_of_frob_comm.solution
