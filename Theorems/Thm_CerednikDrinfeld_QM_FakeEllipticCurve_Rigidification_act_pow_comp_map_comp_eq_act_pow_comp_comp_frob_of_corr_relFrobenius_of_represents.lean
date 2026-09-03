import Definitions.Def_CerednikDrinfeld_QMRigidification
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_act_pow_comp_map_comp_eq_act_pow_comp_comp_frob_of_corr_relFrobenius_of_represents
attribute [-instance] MvFormalGroup.Points.instNeg MvFormalGroup.Points.instZero MvFormalGroup.Points.instAdd MvFormalGroup.Points.instAddCommGroup MvFormalGroup.Points.instAddGroup
attribute [-simp] MvFormalGroup.Points.mk.injEq MvFormalGroup.Points.mk.sizeOf_spec

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld CerednikDrinfeld.QM
  CerednikDrinfeld.SpecialFormal

theorem CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.act_pow_comp_map_comp_eq_act_pow_comp_comp_frob_of_corr_relFrobenius_of_represents
    {r N : ℕ} [Fact r.Prime]
    (𝒪 : Type) [CommRing 𝒪] (π : 𝒪) (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π})
    (Onr : Type) [CommRing Onr] [Algebra 𝒪 Onr] (Fr : Onr ≃ₐ[𝒪] Onr)
    (hFr : ∀ x : Onr, Fr x - x ^ r ∈ Ideal.span {algebraMap 𝒪 Onr π})
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    (coord : ↥Λ → Zp2 r × Zp2 r) (hcoord : IsOrderCoord Λ r coord)
    (A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))
    (X₀ : FormalODModule r (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))
    (θ₀ : RelativeGroupLaw.FormalCoordinates A₀.f 2) (hA₀ : A₀.IsFormalModuleVia coord X₀ θ₀)

    (A₀r : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π})) (prA : A₀r.A ⟶ A₀.A)
    (hprA : FakeEllipticCurve.IsPullbackVia (FakeEllipticCurve.Rigidification.residueLeg π (Fr : Onr →ₐ[𝒪] Onr)) A₀ A₀r prA)
    (F : A₀.A ⟶ A₀r.A) (hF : F ≫ A₀r.f = A₀.f)
    (hFlin : ∀ x : ↥Λ, A₀.act x ≫ F = F ≫ A₀r.act x)
    (hFfrob : ∀ (C : Type) [CommRing C] [CharP C r] (x : Spec (CommRingCat.of C) ⟶ A₀.A),
        x ≫ F ≫ prA = Spec.map (CommRingCat.ofHom (frobenius C r)) ≫ x)

    (L : Type) [CommRing L] [Algebra 𝒪 L] (ψ ψ' : Onr →ₐ[𝒪] L) (hψ' : ψ' = ψ.comp (Fr : Onr →ₐ[𝒪] Onr))
    (E E' : FakeEllipticCurve Λ N L) (q : E.A ⟶ E'.A) (hq : q ≫ E'.f = E.f)
    (hmul : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of L)) (P Q : SchemeHomOver t E.f),
      mapPt q hq (E.L.mul t P Q) = E'.L.mul t (mapPt q hq P) (mapPt q hq Q))
    (hlin : ∀ x : ↥Λ, E.act x ≫ q = q ≫ E'.act x)
    (ρ : FakeEllipticCurve.Rigidification r π A₀ ψ E) (ρ' : FakeEllipticCurve.Rigidification r π A₀ ψ' E')
    (qb : ρ.Eb.A ⟶ ρ'.Eb.A) (hqb : qb ≫ ρ'.gb = ρ.gb ≫ q) (hqbf : qb ≫ ρ'.Eb.f = ρ.Eb.f)
    (uA : ρ'.Ab.A ⟶ A₀r.A)
    (huA : FakeEllipticCurve.IsPullbackVia (FakeEllipticCurve.Rigidification.residueLeg π ψ) A₀r ρ'.Ab uA)
    (huAg : uA ≫ prA = ρ'.gA)
    (Fb : ρ.Ab.A ⟶ ρ'.Ab.A) (hFb : Fb ≫ uA = ρ.gA ≫ F) (hFbf : Fb ≫ ρ'.Ab.f = ρ.Ab.f)
    (i j : ℕ)
    (hcorr : qb ≫ ρ'.φ ≫ ρ'.Ab.act ⟨(((r ^ i : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = ρ.φ ≫ Fb ≫ ρ'.Ab.act ⟨(((r ^ j : ℕ) : ℤ) : ℚ), hΛℤ _⟩)

    (X : FormalODModule r L) (θ : RelativeGroupLaw.FormalCoordinates E.f 2) (hX : E.IsFormalModuleVia coord X θ)
    (X' : FormalODModule r L) (θ' : RelativeGroupLaw.FormalCoordinates E'.f 2) (hX' : E'.IsFormalModuleVia coord X' θ')
    (σ : Series (L ⧸ Ideal.span {algebraMap 𝒪 L π})) (hσ0 : ∀ i, MvPowerSeries.constantCoeff (σ i) = 0)
    (hσ : (∀ (B'' : Type) [CommRing B''] [Algebra (L ⧸ Ideal.span {algebraMap 𝒪 L π}) B''] [Algebra L B'']
            [Algebra (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) B''],
            algebraMap L B'' = (algebraMap (L ⧸ Ideal.span {algebraMap 𝒪 L π}) B'').comp (Ideal.Quotient.mk _) →
            algebraMap (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) B'' =
              (algebraMap (L ⧸ Ideal.span {algebraMap 𝒪 L π}) B'').comp (FakeEllipticCurve.Rigidification.residueLeg π ψ) →
            ∀ (J : Ideal B'') (m : ℕ), J ^ (m + 1) = ⊥ → ∀ s : Fin 2 → B'', (∀ i, s i ∈ J) →
              ∀ PA : Spec (CommRingCat.of B'') ⟶ ρ.Ab.A,
                PA ≫ ρ.Ab.f = Spec.map (CommRingCat.ofHom (algebraMap (L ⧸ Ideal.span {algebraMap 𝒪 L π}) B'')) →
                PA ≫ ρ.gA = (θ₀ B'' s).1 →
                  PA ≫ ρ.φ' ≫ ρ.gb = (θ B'' (fun i => MvFormalGroup.nilEval m (σ i) s)).1))
    (σ' : Series (L ⧸ Ideal.span {algebraMap 𝒪 L π})) (hσ'0 : ∀ i, MvPowerSeries.constantCoeff (σ' i) = 0)
    (hσ' : (∀ (B'' : Type) [CommRing B''] [Algebra (L ⧸ Ideal.span {algebraMap 𝒪 L π}) B''] [Algebra L B'']
            [Algebra (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) B''],
            algebraMap L B'' = (algebraMap (L ⧸ Ideal.span {algebraMap 𝒪 L π}) B'').comp (Ideal.Quotient.mk _) →
            algebraMap (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) B'' =
              (algebraMap (L ⧸ Ideal.span {algebraMap 𝒪 L π}) B'').comp (FakeEllipticCurve.Rigidification.residueLeg π ψ') →
            ∀ (J : Ideal B'') (m : ℕ), J ^ (m + 1) = ⊥ → ∀ s : Fin 2 → B'', (∀ i, s i ∈ J) →
              ∀ PA : Spec (CommRingCat.of B'') ⟶ ρ'.Ab.A,
                PA ≫ ρ'.Ab.f = Spec.map (CommRingCat.ofHom (algebraMap (L ⧸ Ideal.span {algebraMap 𝒪 L π}) B'')) →
                PA ≫ ρ'.gA = (θ₀ B'' s).1 →
                  PA ≫ ρ'.φ' ≫ ρ'.gb = (θ' B'' (fun i => MvFormalGroup.nilEval m (σ' i) s)).1))
    (qhat : Series L) (hq0 : ∀ i, MvPowerSeries.constantCoeff (qhat i) = 0)
    (hrep : ∀ (B'' : Type) [CommRing B''] [Algebra L B''] (J : Ideal B'') (n : ℕ), J ^ (n + 1) = ⊥ →
        ∀ s : Fin 2 → B'', (∀ i, s i ∈ J) →
          (θ B'' s).1 ≫ q = (θ' B'' (fun i => MvFormalGroup.nilEval n (qhat i) s)).1) :
    ((X'.map (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 L π}))).act (((r : ℕ) : Zp2 r) ^ (ρ'.d + i))).comp
        ((Series.map (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 L π})) qhat).comp σ) =
      ((X'.map (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 L π}))).act (((r : ℕ) : Zp2 r) ^ (ρ.d + j))).comp
        (σ'.comp fun i => (MvPowerSeries.X i : MvPowerSeries (Fin 2) (L ⧸ Ideal.span {algebraMap 𝒪 L π})) ^ r) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_act_pow_comp_map_comp_eq_act_pow_comp_comp_frob_of_corr_relFrobenius_of_represents.solution
