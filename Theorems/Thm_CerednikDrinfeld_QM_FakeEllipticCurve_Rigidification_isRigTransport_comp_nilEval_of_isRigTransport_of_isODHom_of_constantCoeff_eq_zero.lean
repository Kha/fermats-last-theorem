import Definitions.Def_CerednikDrinfeld_QMRigidification
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_isRigTransport_comp_nilEval_of_isRigTransport_of_isODHom_of_constantCoeff_eq_zero

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld CerednikDrinfeld.QM
  CerednikDrinfeld.SpecialFormal
open scoped Quaternion

theorem CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.isRigTransport_comp_nilEval_of_isRigTransport_of_isODHom_of_constantCoeff_eq_zero
    {r : ℕ} [Fact r.Prime] {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}

    (𝒪 : Type) [CommRing 𝒪] (π : 𝒪) (Onr : Type) [CommRing Onr] [Algebra 𝒪 Onr]
    (A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))
    (θ₀ : RelativeGroupLaw.FormalCoordinates A₀.f 2)
    (κ : (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) →+* (Onr ⧸ pIdeal r Onr))
    (β₀ : Series (Onr ⧸ pIdeal r Onr))

    {B : Type} [CommRing B] [Algebra 𝒪 B] (ψ : Onr →ₐ[𝒪] B)
    {E : FakeEllipticCurve Λ N B} (ρ : FakeEllipticCurve.Rigidification r π A₀ ψ E)
    (θ : RelativeGroupLaw.FormalCoordinates E.f 2) (j : ℕ)
    {Φ : FormalODModule r (Onr ⧸ pIdeal r Onr)} (t : Rigidified r Φ B)
    (ht : FakeEllipticCurve.Rigidification.IsRigTransport θ₀ κ β₀ ρ θ j t)

    (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π})
    (hβ₀c : ∀ i, MvPowerSeries.constantCoeff (β₀ i) = 0)
    (hρc : ∀ i, MvPowerSeries.constantCoeff (t.ρ i) = 0)

    (Y : FormalODModule r B) (u v : Series B)
    (hu : FormalODModule.IsODHom t.X Y u) (hv : FormalODModule.IsODHom Y t.X v)
    (hvu : v.comp u = Series.id B) (huv : u.comp v = Series.id B)
    (θ' : RelativeGroupLaw.FormalCoordinates E.f 2)
    (hθ' : ∀ (B'' : Type) [CommRing B''] [Algebra B B''] (J : Ideal B'') (n : ℕ), J ^ (n + 1) = ⊥ →
      ∀ s : Fin 2 → B'', (∀ i, s i ∈ J) →
        θ' B'' s = θ B'' (fun i => MvFormalGroup.nilEval n (v i) s)) :
    FakeEllipticCurve.Rigidification.IsRigTransport θ₀ κ β₀ ρ θ' j
      ({ X := Y, n := t.n, ρ := (u.map (Ideal.Quotient.mk (pIdeal r B))).comp t.ρ } : Rigidified r Φ B) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_isRigTransport_comp_nilEval_of_isRigTransport_of_isODHom_of_constantCoeff_eq_zero.solution
