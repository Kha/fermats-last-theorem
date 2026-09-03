import Definitions.Def_GoodReductionJacobian_BareDeformation
import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_exists_bareDeformation_dualNumber_isPullback_fst_comp_eq_id
attribute [-simp] AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst RegularLocalRingQuotientAscent.dualNumberFst_apply

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing Scheme.TwoAffineOpenCover CerednikDrinfeld.QM

theorem GoodReductionJacobian.exists_bareDeformation_dualNumber_isPullback_fst_comp_eq_id
    (k : Type) [Field k]
    {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k)) (L : RelativeGroupLaw k f) (hc : L.IsCommutative)
    (hA : AbelianSchemePropertyBundle k f)

    (𝒦 : A.OrderedAffineCover) (i₀ : 𝒦.ι)
    (eA : Spec (CommRingCat.of k) ⟶ ↑(𝒦.U i₀)) (heA : eA ≫ (𝒦.U i₀).ι = (L.one (𝟙 _)).1) :
    letI : Algebra (DualNumber k) k := (TrivSqZeroExt.fstHom k k k).toRingHom.toAlgebra
    ∃ (D₀ : BareDeformation f L (DualNumber k)) (_ : IsSeparated D₀.f)
      (π : D₀.A ⟶ A) (_ : IsAffineHom π)
      (hπ : CategoryTheory.IsPullback π D₀.f f (Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k)))))
      (_ : D₀.g ≫ π = 𝟙 A),

      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (DualNumber k))) (P Q : SchemeHomOver t D₀.f),
        (D₀.L.mul t P Q).1 ≫ π =
          (L.mul (t ≫ Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k))))
            ⟨P.1 ≫ π, by rw [Category.assoc, hπ.w, ← Category.assoc, P.2]⟩
            ⟨Q.1 ≫ π, by rw [Category.assoc, hπ.w, ← Category.assoc, Q.2]⟩).1) ∧

      (∀ (φ : A ⟶ A) (hφ : φ ≫ f = f),
        ∃ (φ₀ : D₀.A ⟶ D₀.A) (hφ₀ : φ₀ ≫ D₀.f = D₀.f), φ ≫ D₀.g = D₀.g ≫ φ₀ ∧ φ₀ ≫ π = π ≫ φ ∧
          ((∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t f),
              pushPt φ hφ (L.mul t P Q) = L.mul t (pushPt φ hφ P) (pushPt φ hφ Q)) →
            ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (DualNumber k))) (P Q : SchemeHomOver t D₀.f),
              pushPt φ₀ hφ₀ (D₀.L.mul t P Q) = D₀.L.mul t (pushPt φ₀ hφ₀ P) (pushPt φ₀ hφ₀ Q))) ∧

      (∀ c : k, ∃ k₀ : D₀.A ⟶ D₀.A,
        CategoryTheory.IsPullback k₀ D₀.f D₀.f
          (Spec.map (CommRingCat.ofHom (TrivSqZeroExt.map (R' := k) (c • (LinearMap.id : k →ₗ[k] k))).toRingHom)) ∧
        D₀.g ≫ k₀ = D₀.g ∧ k₀ ≫ π = π ∧
        pullback.fst D₀.f (specMap (DualNumber k) (ResidueField (DualNumber k))) ≫ k₀ =
          pullback.fst D₀.f (specMap (DualNumber k) (ResidueField (DualNumber k)))) ∧

      (∀ (φ₀ : D₀.A ⟶ D₀.A) (hφ₀ : φ₀ ≫ D₀.f = D₀.f),
        ∃ (ψ : pullback D₀.f (specMap (DualNumber k) (ResidueField (DualNumber k))) ⟶
            pullback D₀.f (specMap (DualNumber k) (ResidueField (DualNumber k))))
          (hψ : ψ ≫ (pullback.snd D₀.f (specMap (DualNumber k) (ResidueField (DualNumber k)))) = (pullback.snd D₀.f (specMap (DualNumber k) (ResidueField (DualNumber k))))),
          ψ ≫ pullback.fst D₀.f (specMap (DualNumber k) (ResidueField (DualNumber k))) =
            pullback.fst D₀.f (specMap (DualNumber k) (ResidueField (DualNumber k))) ≫ φ₀ ∧
          ((∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (DualNumber k))) (P Q : SchemeHomOver t D₀.f),
              pushPt φ₀ hφ₀ (D₀.L.mul t P Q) = D₀.L.mul t (pushPt φ₀ hφ₀ P) (pushPt φ₀ hφ₀ Q)) →
            ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (ResidueField (DualNumber k))))
              (P Q : SchemeHomOver t (pullback.snd D₀.f (specMap (DualNumber k) (ResidueField (DualNumber k))))),
              pushPt ψ hψ ((RelativeGroupLaw.baseChange (specMap (DualNumber k) (ResidueField (DualNumber k))) D₀.L).mul t P Q) = (RelativeGroupLaw.baseChange (specMap (DualNumber k) (ResidueField (DualNumber k))) D₀.L).mul t (pushPt ψ hψ P) (pushPt ψ hψ Q))) ∧

      (∃ e₀ : Spec (CommRingCat.of (DualNumber k)) ⟶ ↑((𝒦.comap π).U i₀),
        e₀ ≫ ((𝒦.comap π).U i₀).ι = (D₀.L.one (𝟙 _)).1) := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_exists_bareDeformation_dualNumber_isPullback_fst_comp_eq_id.solution
