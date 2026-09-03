import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_lev_finrank_eq_sq_forall_factorsThrough_iff_of_isPullback_of_isNilpotent_ker
attribute [-simp] GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
p2m_open "CategoryTheory AlgebraicGeometry~isFinite_and_etale_comp_of_isOpenImmersion_of_isClosed_range QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra GoodReductionJacobian"

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_lev_finrank_eq_sq_forall_factorsThrough_iff_of_isPullback_of_isNilpotent_ker
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    {S S₀ : Type} [CommRing S] [CommRing S₀]
    (p : S →+* S₀) (hp : Function.Surjective p) (hI : IsNilpotent (RingHom.ker p))
    (E₀ : FakeEllipticCurve Λ N S₀)
    {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)} [IsSeparated f]
    (L : RelativeGroupLaw S f) (hcomm : L.IsCommutative)
    (hN : IsUnit ((N : ℕ) : S))
    (hfin : IsFinite (L.schemeKerStr N)) (het : Etale (L.schemeKerStr N))
    (g : E₀.A ⟶ A) (hg : CategoryTheory.IsPullback g E₀.f f (Spec.map (CommRingCat.ofHom p)))
    (hmul : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S₀)) (P Q : SchemeHomOver t' E₀.f),
      (E₀.L.mul t' P Q).1 ≫ g =
        (L.mul (t' ≫ Spec.map (CommRingCat.ofHom p))
          ⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, Q.2]⟩).1) :
    ∃ (C : Scheme.{0}) (lev : C ⟶ A),
      IsClosedImmersion lev ∧

      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t f),
        FactorsThrough lev P → FactorsThrough lev Q →
          FactorsThrough lev (L.mul t P Q) ∧ FactorsThrough lev (L.inv t P)) ∧
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)), FactorsThrough lev (L.one t)) ∧
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t f),
        FactorsThrough lev P → nsmulPt L t N P = L.one t) ∧

      IsFinite (lev ≫ f) ∧ Flat (lev ≫ f) ∧ LocallyOfFinitePresentation (lev ≫ f) ∧
      (∀ s : ↥(Spec (CommRingCat.of S)), (lev ≫ f).finrank s = N ^ 2) ∧

      (∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S →+* k), (N : k) ≠ 0 →
        ∃ e : ZMod N × ZMod N ≃ {P : SchemeHomOver (geomPoint k sk) f // FactorsThrough lev P},
          ∀ x y : ZMod N × ZMod N,
            (e (x + y) : SchemeHomOver (geomPoint k sk) f) = L.mul (geomPoint k sk) (e x) (e y)) ∧

      (∀ {T : Scheme.{0}} (t₀ : T ⟶ Spec (CommRingCat.of S₀)) (P₀ : SchemeHomOver t₀ E₀.f),
        FactorsThrough E₀.lev P₀ ↔ ∃ Q : T ⟶ C, Q ≫ lev = P₀.1 ≫ g) ∧

      (∀ (α : A ⟶ A) (hα : α ≫ f = f),
        (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t f),
          pushPt α hα (L.mul t P Q) = L.mul t (pushPt α hα P) (pushPt α hα Q)) →
        ∀ (β : E₀.A ⟶ E₀.A) (hβ : β ≫ E₀.f = E₀.f), β ≫ g = g ≫ α →
        (∀ {T : Scheme.{0}} (t₀ : T ⟶ Spec (CommRingCat.of S₀)) (P₀ : SchemeHomOver t₀ E₀.f),
          FactorsThrough E₀.lev P₀ → FactorsThrough E₀.lev (pushPt β hβ P₀)) →
        ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t f),
          FactorsThrough lev P → FactorsThrough lev (pushPt α hα P)) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_lev_finrank_eq_sq_forall_factorsThrough_iff_of_isPullback_of_isNilpotent_ker.solution
