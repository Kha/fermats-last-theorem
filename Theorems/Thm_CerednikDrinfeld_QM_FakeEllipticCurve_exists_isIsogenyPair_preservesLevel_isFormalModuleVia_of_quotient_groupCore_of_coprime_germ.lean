import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_CerednikDrinfeld_QMIsogeny
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isIsogenyPair_preservesLevel_isFormalModuleVia_of_quotient_groupCore_of_coprime_germ

set_option autoImplicit false

open scoped Quaternion TensorProduct NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.SpecialFormal NeronModelInfra GoodReductionJacobian

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_isIsogenyPair_preservesLevel_isFormalModuleVia_of_quotient_groupCore_of_coprime_germ
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {r : ℕ} [Fact r.Prime]
    (coord : ↥Λ → Zp2 r × Zp2 r)
    (k : Type) [Field k] [IsAlgClosed k] (E₀ : FakeEllipticCurve Λ N k) (hΛ : QuaternionAlgebra.IsOrder Λ)
    (X₀ : FormalODModule r k) (θ₀ : RelativeGroupLaw.FormalCoordinates E₀.f 2)
    (n : ℕ) (hnN : Nat.Coprime n N)

    (K₀ : Scheme.{0}) (ι : K₀ ⟶ E₀.A)
    (hK_torsion : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t E₀.f),
      FactorsThrough ι P → nsmulPt E₀.L t n P = E₀.L.one t)

    (A : Scheme.{0}) (f : A ⟶ Spec (CommRingCat.of k)) (L : RelativeGroupLaw k f) (act : ↥Λ → (A ⟶ A))
    (hact : ∀ x : ↥Λ, act x ≫ f = f)
    (p : E₀.A ⟶ A) (hp : p ≫ f = E₀.f) (ψ : A ⟶ E₀.A) (hψ : ψ ≫ E₀.f = f)
    (hcomm : L.IsCommutative)
    (hbundle : AbelianSchemePropertyBundle k f)
    (hdim : ∀ s : ↥(Spec (CommRingCat.of k)), topologicalKrullDim ↥(f.base ⁻¹' {s}) = 2)
    (hact_hom : ∀ (x : ↥Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t f),
      pushPt (act x) (hact x) (L.mul t P Q) = L.mul t (pushPt (act x) (hact x) P) (pushPt (act x) (hact x) Q))
    (hact_one : ∀ h : (1 : ℍ[ℚ, a, b]) ∈ Λ, act ⟨1, h⟩ = 𝟙 A)
    (hact_mul : ∀ (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ),
      act ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = act y ≫ act x)
    (hact_add : ∀ (x y : ↥Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t f),
      pushPt (act (x + y)) (hact (x + y)) P = L.mul t (pushPt (act x) (hact x) P) (pushPt (act y) (hact y) P))
    (hp_hom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t E₀.f),
      mapPt p hp (E₀.L.mul t P Q) = L.mul t (mapPt p hp P) (mapPt p hp Q))
    (hequiv : ∀ x : ↥Λ, E₀.act x ≫ p = p ≫ act x)
    (hp_finite : IsFinite p)
    (hker : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t E₀.f),
      mapPt p hp P = L.one t ↔ FactorsThrough ι P)
    (hψ_hom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t f),
      mapPt ψ hψ (L.mul t P Q) = E₀.L.mul t (mapPt ψ hψ P) (mapPt ψ hψ Q))
    (hψ_lin : ∀ x : ↥Λ, act x ≫ ψ = ψ ≫ E₀.act x)
    (hψp : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t E₀.f),
      mapPt ψ hψ (mapPt p hp P) = nsmulPt E₀.L t n P)
    (hpψ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (Q : SchemeHomOver t f),
      mapPt p hp (mapPt ψ hψ Q) = nsmulPt L t n Q)

    (htrace : ∀ (k' : Type) [Field k'] [IsAlgClosed k'] (sk : k →+* k')
      (V : Type) [AddCommGroup V] [Module k' V] [Module.Finite k' V] (τ : V → SchemeHomOver (tangentBase k' sk) f),
      Function.Injective τ →
      (∀ P : SchemeHomOver (tangentBase k' sk) f, P ∈ Set.range τ ↔ IsTangentVector L k' sk P) →
      (∀ v w : V, τ (v + w) = L.mul (tangentBase k' sk) (τ v) (τ w)) →
      (∀ (c : k') (v : V), (τ (c • v)).1 = tangentScale k' c ≫ (τ v).1) →
      ∀ (m : ↥Λ) (Φ : V →ₗ[k'] V), (∀ v : V, τ (Φ v) = pushPt (act m) (hact m) (τ v)) →
      ∀ n' : ℤ, (m : ℍ[ℚ, a, b]) + star (m : ℍ[ℚ, a, b]) = ((n' : ℚ) : ℍ[ℚ, a, b]) →
        LinearMap.trace k' V Φ = (n' : k'))

    (X : FormalODModule r k) (θ : RelativeGroupLaw.FormalCoordinates f 2) (hθ : L.IsFormalCoordinates X.F θ)
    (hθact : ∀ (B' : Type) [CommRing B'] [Algebra k B'] (J : Ideal B') (m : ℕ), J ^ (m + 1) = ⊥ →
      ∀ (x : ↥Λ) (s : Fin 2 → B'), (∀ i, s i ∈ J) →
        θ B' (fun i => MvFormalGroup.nilEval m
            (Series.addVia X.F (X.act (coord x).1) ((X.act (coord x).2).comp X.varpi) i) s) =
          pushPt (act x) (hact x) (θ B' s))
    (γp : Series k) (hγp : FormalODModule.IsODHom X₀ X γp)
    (hgerm : ∀ (B'' : Type) [CommRing B''] [Algebra k B''] (J : Ideal B'') (m : ℕ), J ^ (m + 1) = ⊥ →
      ∀ s : Fin 2 → B'', (∀ i, s i ∈ J) →
        (θ₀ B'' s).1 ≫ p = (θ B'' (fun i => MvFormalGroup.nilEval m (γp i) s)).1) :
    ∃ (E : FakeEllipticCurve Λ N k) (q : E₀.A ⟶ E.A) (hq : q ≫ E.f = E₀.f) (q' : E.A ⟶ E₀.A) (hq' : q' ≫ E₀.f = E.f)
      (θE : RelativeGroupLaw.FormalCoordinates E.f 2),
      FakeEllipticCurve.IsIsogenyPair n E₀ E q q' ∧
      FakeEllipticCurve.PreservesLevel E₀ E q hq ∧ FakeEllipticCurve.PreservesLevel E E₀ q' hq' ∧
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t E₀.f),
        mapPt q hq P = E.L.one t ↔ FactorsThrough ι P) ∧
      E.IsFormalModuleVia coord X θE ∧
      (∀ (B'' : Type) [CommRing B''] [Algebra k B''] (J : Ideal B'') (m : ℕ), J ^ (m + 1) = ⊥ →
        ∀ s : Fin 2 → B'', (∀ i, s i ∈ J) →
          (θ₀ B'' s).1 ≫ q = (θE B'' (fun i => MvFormalGroup.nilEval m (γp i) s)).1) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isIsogenyPair_preservesLevel_isFormalModuleVia_of_quotient_groupCore_of_coprime_germ.solution
