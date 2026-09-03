import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_CerednikDrinfeld_QMIsogeny
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isFormalCoordinates_quotient_comp_eq_nilEval_of_factorsThrough_iff_nilEval_eq_zero_of_isAlgClosed
attribute [-instance] MvFormalGroup.Points.instNeg MvFormalGroup.Points.instZero MvFormalGroup.Points.instAdd MvFormalGroup.Points.instAddCommGroup MvFormalGroup.Points.instAddGroup instTopologicallyFGOfFiniteType
attribute [-simp] MvFormalGroup.Points.mk.injEq MvFormalGroup.Points.mk.sizeOf_spec GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory AlgebraicGeometry CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.SpecialFormal NeronModelInfra GoodReductionJacobian

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_isFormalCoordinates_quotient_comp_eq_nilEval_of_factorsThrough_iff_nilEval_eq_zero_of_isAlgClosed
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {r : ℕ} [Fact r.Prime]
    (hΛ1 : (1 : ℍ[ℚ, a, b]) ∈ Λ) (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    (coord : ↥Λ → Zp2 r × Zp2 r) (hcoord : IsOrderCoord Λ r coord)
    (k : Type) [Field k] [IsAlgClosed k] (hkr : IsNilpotent ((r : ℕ) : k))

    (A : FakeEllipticCurve Λ N k) (XA : FormalODModule r k) (θA : RelativeGroupLaw.FormalCoordinates A.f 2)
    (hA : A.IsFormalModuleVia coord XA θA) (hA4 : XA.HasHeight 4)

    (Y : FormalODModule r k) (γ : Series k) (h : ℕ) (hγ : FormalODModule.IsIsogenyOfHeight XA Y γ h)

    (K : Scheme.{0}) (ι : K ⟶ A.A) (hι_closed : IsClosedImmersion ι)
    (hι_finite : IsFinite (ι ≫ A.f)) (hι_flat : Flat (ι ≫ A.f)) (hι_fp : LocallyOfFinitePresentation (ι ≫ A.f))
    (hι_rank : ∀ y : ↥(Spec (CommRingCat.of k)), (ι ≫ A.f).finrank y = r ^ h)
    (hK_one : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)), FactorsThrough ι (A.L.one t))
    (hK_sub : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t A.f),
      FactorsThrough ι P → FactorsThrough ι Q → FactorsThrough ι (A.L.mul t P Q) ∧ FactorsThrough ι (A.L.inv t P))
    (hK_stable : ∀ (x : ↥Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t A.f),
      FactorsThrough ι P → FactorsThrough ι (pushPt (A.act x) (A.act_over x) P))
    (c : ℕ)
    (hK_torsion : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t A.f),
      FactorsThrough ι P → nsmulPt A.L t (r ^ c) P = A.L.one t)
    (hKγ : ∀ (B'' : Type) [CommRing B''] [Algebra k B''] (J : Ideal B'') (n : ℕ), J ^ (n + 1) = ⊥ →
      ∀ s : Fin 2 → B'', (∀ i, s i ∈ J) →
        (FactorsThrough ι (θA B'' s) ↔ ∀ i, MvFormalGroup.nilEval n (γ i) s = 0))

    (A' : Scheme.{0}) (f' : A' ⟶ Spec (CommRingCat.of k)) (L' : RelativeGroupLaw k f') (act' : ↥Λ → (A' ⟶ A'))
    (hact' : ∀ x : ↥Λ, act' x ≫ f' = f')
    (p : A.A ⟶ A') (hp : p ≫ f' = A.f) (ψ : A' ⟶ A.A) (hψ : ψ ≫ A.f = f')
    (hL'_comm : L'.IsCommutative)
    (hA'_bundle : AbelianSchemePropertyBundle k f')
    (hA'_dim : ∀ s : ↥(Spec (CommRingCat.of k)), topologicalKrullDim ↥(f'.base ⁻¹' {s}) = 2)
    (hact'_mul : ∀ (x : ↥Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t f'),
      pushPt (act' x) (hact' x) (L'.mul t P Q) = L'.mul t (pushPt (act' x) (hact' x) P) (pushPt (act' x) (hact' x) Q))

    (hp_mul : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t A.f),
      mapPt p hp (A.L.mul t P Q) = L'.mul t (mapPt p hp P) (mapPt p hp Q))
    (hp_act : ∀ x : ↥Λ, A.act x ≫ p = p ≫ act' x)
    (hp_finite : IsFinite p) (hp_flat : Flat p) (hp_fp : LocallyOfFinitePresentation p) (hp_surj : Surjective p)
    (hp_ker : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t A.f),
      mapPt p hp P = L'.one t ↔ FactorsThrough ι P)

    (hψ_mul : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t f'),
      mapPt ψ hψ (L'.mul t P Q) = A.L.mul t (mapPt ψ hψ P) (mapPt ψ hψ Q))
    (hψ_act : ∀ x : ↥Λ, act' x ≫ ψ = ψ ≫ A.act x)
    (hψp : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t A.f),
      mapPt ψ hψ (mapPt p hp P) = nsmulPt A.L t (r ^ c) P)
    (hpψ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (Q : SchemeHomOver t f'),
      mapPt p hp (mapPt ψ hψ Q) = nsmulPt L' t (r ^ c) Q)

    (hp_univ : ∀ (X : Scheme.{0}) (gX : X ⟶ Spec (CommRingCat.of k)) (LX : RelativeGroupLaw k gX) (φ : A.A ⟶ X) (hφ : φ ≫ gX = A.f),
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t A.f),
        mapPt φ hφ (A.L.mul t P Q) = LX.mul t (mapPt φ hφ P) (mapPt φ hφ Q)) →
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t A.f),
        FactorsThrough ι P → mapPt φ hφ P = LX.one t) →
      ∃! χ : SchemeHomOver f' gX, p ≫ χ.1 = φ ∧
        ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (u v : SchemeHomOver t f'),
          mapPt χ.1 χ.2 (L'.mul t u v) = LX.mul t (mapPt χ.1 χ.2 u) (mapPt χ.1 χ.2 v)) :
    ∃ θ' : RelativeGroupLaw.FormalCoordinates f' 2,

      L'.IsFormalCoordinates Y.F θ' ∧
      (∀ (B' : Type) [CommRing B'] [Algebra k B'] (J : Ideal B') (m : ℕ), J ^ (m + 1) = ⊥ →
        ∀ (x : ↥Λ) (s : Fin 2 → B'), (∀ i, s i ∈ J) →
          θ' B' (fun i => MvFormalGroup.nilEval m
              (Series.addVia Y.F (Y.act (coord x).1) ((Y.act (coord x).2).comp Y.varpi) i) s) =
            pushPt (act' x) (hact' x) (θ' B' s)) ∧

      (∀ (B'' : Type) [CommRing B''] [Algebra k B''] (J : Ideal B'') (m : ℕ), J ^ (m + 1) = ⊥ →
        ∀ s : Fin 2 → B'', (∀ i, s i ∈ J) →
          (θA B'' s).1 ≫ p = (θ' B'' (fun i => MvFormalGroup.nilEval m (γ i) s)).1) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isFormalCoordinates_quotient_comp_eq_nilEval_of_factorsThrough_iff_nilEval_eq_zero_of_isAlgClosed.solution
