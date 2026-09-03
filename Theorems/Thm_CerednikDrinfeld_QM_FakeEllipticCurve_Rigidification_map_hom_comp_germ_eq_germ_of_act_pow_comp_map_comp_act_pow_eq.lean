import Definitions.Def_CerednikDrinfeld_QMRigidification
import Definitions.Def_CerednikDrinfeld_SpecialFormalFunctorG
import Definitions.Def_CerednikDrinfeld_CosetGraphAtPrime
import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_CerednikDrinfeld_QMIsogeny
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_map_hom_comp_germ_eq_germ_of_act_pow_comp_map_comp_act_pow_eq

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra IsDedekindDomain CerednikDrinfeld CerednikDrinfeld.QM
  CerednikDrinfeld.FormalOmega CerednikDrinfeld.SpecialFormal NeronModelInfra GoodReductionJacobian

theorem CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.map_hom_comp_germ_eq_germ_of_act_pow_comp_map_comp_act_pow_eq
    {r N : ℕ} [Fact r.Prime] [NeZero N] (hrN : ¬ r ∣ N)
    (𝒪 : Type) [CommRing 𝒪] (π : 𝒪) (Onr : Type) [CommRing Onr] [Algebra 𝒪 Onr]
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    (coord : ↥Λ → Zp2 r × Zp2 r) (hcoord : IsOrderCoord Λ r coord)
    (A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))

    (k : Type) [Field k] [IsAlgClosed k] [Algebra 𝒪 k] (hk : IsNilpotent (algebraMap 𝒪 k π)) (hkr : IsNilpotent ((r : ℕ) : k))
    (ψ : Onr →ₐ[𝒪] k)
    (x x' : FakeEllipticCurve.RigidifiedCurve r π A₀ k ψ)
    (X X' : FormalODModule r k)
    (θ : RelativeGroupLaw.FormalCoordinates x.1.f 2) (θ' : RelativeGroupLaw.FormalCoordinates x'.1.f 2)
    (T₀ : FormalODModule.Hom X X')

    (X₀ : FormalODModule r (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π})) (θ₀ : RelativeGroupLaw.FormalCoordinates A₀.f 2)
    (hA₀ : A₀.IsFormalModuleVia coord X₀ θ₀)
    (θA : RelativeGroupLaw.FormalCoordinates x.2.Ab.f 2)
    (hθA : x.2.Ab.IsFormalModuleVia coord (X₀.map (FakeEllipticCurve.Rigidification.residueLeg π ψ)) θA)
    (hθAg : ∀ (B'' : Type) [CommRing B''] [Algebra (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) B''] [Algebra (k ⧸ Ideal.span {algebraMap 𝒪 k π}) B''],
      algebraMap (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) B'' = (algebraMap (k ⧸ Ideal.span {algebraMap 𝒪 k π}) B'').comp (FakeEllipticCurve.Rigidification.residueLeg π ψ) →
      ∀ (s : Fin 2 → B''), (∀ i, IsNilpotent (s i)) → (θA B'' s).1 ≫ x.2.gA = (θ₀ B'' s).1)

    (θE : RelativeGroupLaw.FormalCoordinates x.2.Eb.f 2) (θE' : RelativeGroupLaw.FormalCoordinates x'.2.Eb.f 2)
    (hθE : x.2.Eb.IsFormalModuleVia coord (X.map (algebraMap k (k ⧸ Ideal.span {algebraMap 𝒪 k π}))) θE)
    (hθE' : x'.2.Eb.IsFormalModuleVia coord (X'.map (algebraMap k (k ⧸ Ideal.span {algebraMap 𝒪 k π}))) θE')
    (hθEg : ∀ (B'' : Type) [CommRing B''] [Algebra k B''] [Algebra (k ⧸ Ideal.span {algebraMap 𝒪 k π}) B'']
      [IsScalarTower k (k ⧸ Ideal.span {algebraMap 𝒪 k π}) B''] (s : Fin 2 → B''),
      (∀ i, IsNilpotent (s i)) → (θE B'' s).1 ≫ x.2.gb = (θ B'' s).1)
    (hθEg' : ∀ (B'' : Type) [CommRing B''] [Algebra k B''] [Algebra (k ⧸ Ideal.span {algebraMap 𝒪 k π}) B'']
      [IsScalarTower k (k ⧸ Ideal.span {algebraMap 𝒪 k π}) B''] (s : Fin 2 → B''),
      (∀ i, IsNilpotent (s i)) → (θE' B'' s).1 ≫ x'.2.gb = (θ' B'' s).1)

    (v : x.2.Ab.A ⟶ x'.2.Ab.A) (hv : FakeEllipticCurve.IsPullbackVia (RingHom.id _) x'.2.Ab x.2.Ab v) (hvg : v ≫ x'.2.gA = x.2.gA)

    (κ : (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) →+* (Onr ⧸ pIdeal r Onr))
    (κB : (k ⧸ Ideal.span {algebraMap 𝒪 k π}) →+* (k ⧸ pIdeal r k))
    (hκB : κB.comp (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 k π})) = Ideal.Quotient.mk (pIdeal r k))
    (hκB' : κB.comp (FakeEllipticCurve.Rigidification.residueLeg π ψ) = (residueMap (ψ : Onr →+* k)).comp κ)
    (σ σ' : Series (k ⧸ Ideal.span {algebraMap 𝒪 k π}))
    (hσ0 : ∀ i, MvPowerSeries.constantCoeff (σ i) = 0) (hσ'0 : ∀ i, MvPowerSeries.constantCoeff (σ' i) = 0)
    (hσ : (∀ (B'' : Type) [CommRing B''] [Algebra (k ⧸ Ideal.span {algebraMap 𝒪 k π}) B''] [Algebra k B''] [Algebra (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) B''],
        algebraMap k B'' = (algebraMap (k ⧸ Ideal.span {algebraMap 𝒪 k π}) B'').comp (Ideal.Quotient.mk _) →
        algebraMap (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) B'' =
          (algebraMap (k ⧸ Ideal.span {algebraMap 𝒪 k π}) B'').comp (FakeEllipticCurve.Rigidification.residueLeg π ψ) →
        ∀ (J : Ideal B'') (m : ℕ), J ^ (m + 1) = ⊥ → ∀ s : Fin 2 → B'', (∀ i, s i ∈ J) →
          ∀ PA : Spec (CommRingCat.of B'') ⟶ x.2.Ab.A,
            PA ≫ x.2.Ab.f = Spec.map (CommRingCat.ofHom (algebraMap (k ⧸ Ideal.span {algebraMap 𝒪 k π}) B'')) →
            PA ≫ x.2.gA = (θ₀ B'' s).1 →
              PA ≫ x.2.φ' ≫ x.2.gb = (θ B'' (fun i => MvFormalGroup.nilEval m (σ i) s)).1))
    (hσ' : (∀ (B'' : Type) [CommRing B''] [Algebra (k ⧸ Ideal.span {algebraMap 𝒪 k π}) B''] [Algebra k B''] [Algebra (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) B''],
        algebraMap k B'' = (algebraMap (k ⧸ Ideal.span {algebraMap 𝒪 k π}) B'').comp (Ideal.Quotient.mk _) →
        algebraMap (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) B'' =
          (algebraMap (k ⧸ Ideal.span {algebraMap 𝒪 k π}) B'').comp (FakeEllipticCurve.Rigidification.residueLeg π ψ) →
        ∀ (J : Ideal B'') (m : ℕ), J ^ (m + 1) = ⊥ → ∀ s : Fin 2 → B'', (∀ i, s i ∈ J) →
          ∀ PA : Spec (CommRingCat.of B'') ⟶ x'.2.Ab.A,
            PA ≫ x'.2.Ab.f = Spec.map (CommRingCat.ofHom (algebraMap (k ⧸ Ideal.span {algebraMap 𝒪 k π}) B'')) →
            PA ≫ x'.2.gA = (θ₀ B'' s).1 →
              PA ≫ x'.2.φ' ≫ x'.2.gb = (θ' B'' (fun i => MvFormalGroup.nilEval m (σ' i) s)).1))
    (c₀ c c' : ℕ)
    (heq : (((X'.map (Ideal.Quotient.mk (pIdeal r k))).act ((r : Zp2 r) ^ c)).comp
          ((T₀.toSeries.map (Ideal.Quotient.mk (pIdeal r k))).comp (σ.map κB))).comp
        (((X₀.map κ).map (residueMap (ψ : Onr →+* k))).act ((r : Zp2 r) ^ c₀)) =
      (((X'.map (Ideal.Quotient.mk (pIdeal r k))).act ((r : Zp2 r) ^ c')).comp (σ'.map κB)).comp
        (((X₀.map κ).map (residueMap (ψ : Onr →+* k))).act ((r : Zp2 r) ^ c₀))) :
    (T₀.toSeries.map (algebraMap k (k ⧸ Ideal.span {algebraMap 𝒪 k π}))).comp
        (((X.map (algebraMap k (k ⧸ Ideal.span {algebraMap 𝒪 k π}))).act ((r : Zp2 r) ^ c)).comp
          (σ.comp ((X₀.map (FakeEllipticCurve.Rigidification.residueLeg π ψ)).act ((r : Zp2 r) ^ c₀)))) =
      ((X'.map (algebraMap k (k ⧸ Ideal.span {algebraMap 𝒪 k π}))).act ((r : Zp2 r) ^ c')).comp
        (σ'.comp ((X₀.map (FakeEllipticCurve.Rigidification.residueLeg π ψ)).act ((r : Zp2 r) ^ c₀))) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_map_hom_comp_germ_eq_germ_of_act_pow_comp_map_comp_act_pow_eq.solution
