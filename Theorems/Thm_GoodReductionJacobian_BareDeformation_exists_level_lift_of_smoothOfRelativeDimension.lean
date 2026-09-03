import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_GoodReductionJacobian_BareDeformation
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_BareDeformation_exists_level_lift_of_smoothOfRelativeDimension
attribute [-instance] kmfloorsGlue_int_three_isPrime kmfloorsGlue_int_bot_isPrime instTopologicallyFGOfFiniteType
attribute [-simp] GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst RegularLocalRingQuotientAscent.dualNumberFst_apply GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe
attribute [-simp] NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
  CerednikDrinfeld.SpecialFormal IsLocalRing
open scoped Quaternion TensorProduct NumberField
theorem GoodReductionJacobian.BareDeformation.exists_level_lift_of_smoothOfRelativeDimension
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    (B B₀ : Type) [CommRing B] [IsLocalRing B] [IsArtinianRing B] [CommRing B₀] [Algebra B B₀]
    (hπ : Function.Surjective (algebraMap B B₀)) (hker : IsNilpotent (RingHom.ker (algebraMap B B₀)))
    (hN : IsUnit ((N : ℕ) : B))
    (E₀ : FakeEllipticCurve Λ N B₀) (D : BareDeformation E₀.f E₀.L B) [SmoothOfRelativeDimension 2 D.f]
    {ι : Type} (φ : ι → (D.A ⟶ D.A)) (hφ : ∀ i, φ i ≫ D.f = D.f)
    (hφ_hom : ∀ (i : ι) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)) (P Q : SchemeHomOver t D.f),
      pushPt (φ i) (hφ i) (D.L.mul t P Q) = D.L.mul t (pushPt (φ i) (hφ i) P) (pushPt (φ i) (hφ i) Q))
    (φ₀ : ι → (E₀.A ⟶ E₀.A)) (hφ₀ : ∀ i, φ₀ i ≫ E₀.f = E₀.f) (hφg : ∀ i, φ₀ i ≫ D.g = D.g ≫ φ i)
    (hφ₀_stable : ∀ (i : ι) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B₀)) (P : SchemeHomOver t E₀.f),
      FactorsThrough E₀.lev P → FactorsThrough E₀.lev (pushPt (φ₀ i) (hφ₀ i) P)) :
    ∃ (C : Scheme.{0}) (lev : C ⟶ D.A),
      IsClosedImmersion lev ∧
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)) (P Q : SchemeHomOver t D.f),
        FactorsThrough lev P → FactorsThrough lev Q → FactorsThrough lev (D.L.mul t P Q) ∧ FactorsThrough lev (D.L.inv t P)) ∧
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)), FactorsThrough lev (D.L.one t)) ∧
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)) (P : SchemeHomOver t D.f),
        FactorsThrough lev P → nsmulPt D.L t N P = D.L.one t) ∧
      (∀ (i : ι) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)) (P : SchemeHomOver t D.f),
        FactorsThrough lev P → FactorsThrough lev (pushPt (φ i) (hφ i) P)) ∧
      IsFinite (lev ≫ D.f) ∧ Flat (lev ≫ D.f) ∧ LocallyOfFinitePresentation (lev ≫ D.f) ∧
      (∀ s : ↥(Spec (CommRingCat.of B)), (lev ≫ D.f).finrank s = N ^ 2) ∧
      (∀ (k : Type) [Field k] [IsAlgClosed k] (sk : B →+* k), (N : k) ≠ 0 →
        ∃ e : ZMod N × ZMod N ≃ {P : SchemeHomOver (geomPoint k sk) D.f // FactorsThrough lev P},
          ∀ x y : ZMod N × ZMod N,
            (e (x + y) : SchemeHomOver (geomPoint k sk) D.f) = D.L.mul (geomPoint k sk) (e x) (e y)) ∧

      (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of B₀)) (P : SchemeHomOver t' E₀.f),
        FactorsThrough E₀.lev P → ∃ P₀ : T ⟶ C, P₀ ≫ lev = P.1 ≫ D.g) ∧

      (∀ (C' : Scheme.{0}) (lev' : C' ⟶ D.A), IsClosedImmersion lev' →
        (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)) (P : SchemeHomOver t D.f),
          FactorsThrough lev' P → nsmulPt D.L t N P = D.L.one t) →
        IsFinite (lev' ≫ D.f) → Flat (lev' ≫ D.f) → LocallyOfFinitePresentation (lev' ≫ D.f) →
        (∀ s : ↥(Spec (CommRingCat.of B)), (lev' ≫ D.f).finrank s = N ^ 2) →
        (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of B₀)) (P : SchemeHomOver t' E₀.f),
          FactorsThrough E₀.lev P → ∃ P₀ : T ⟶ C', P₀ ≫ lev' = P.1 ≫ D.g) →
        ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)) (P : SchemeHomOver t D.f),
          FactorsThrough lev P ↔ FactorsThrough lev' P) := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_BareDeformation_exists_level_lift_of_smoothOfRelativeDimension.solution
