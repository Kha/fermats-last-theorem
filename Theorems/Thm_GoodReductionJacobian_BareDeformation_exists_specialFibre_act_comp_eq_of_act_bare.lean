import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_GoodReductionJacobian_BareDeformation
import Definitions.Def_GoodReductionJacobian_IsRegluingBy
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import Definitions.Def_AlgebraicGeometry_SquareZeroDeformation
import Definitions.Def_AlgebraicGeometry_SquareZeroRelTangent
import Definitions.Def_AlgebraicGeometry_SmallExtensionPairTangent
import Definitions.Def_AlgebraicGeometry_TangentCoordsOfPair
import Definitions.Def_AlgebraicGeometry_SmallExtensionTangentCoords
import Definitions.Def_AlgebraicGeometry_TangentCoordsOfPairAt
import Definitions.Def_Algebra_PointDerivations
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCochainPullback
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_BareDeformation_exists_specialFibre_act_comp_eq_of_act_bare

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
  CerednikDrinfeld.SpecialFormal IsLocalRing Scheme.TwoAffineOpenCover
open scoped Quaternion TensorProduct NumberField

theorem GoodReductionJacobian.BareDeformation.exists_specialFibre_act_comp_eq_of_act_bare
    (S S₀ : Type) [CommRing S] [IsLocalRing S] [CommRing S₀] [Algebra S S₀]
    (hπ : Function.Surjective (algebraMap S S₀)) (hI : RingHom.ker (algebraMap S S₀) ≤ maximalIdeal S)
    {Λ : Type} [Ring Λ]
    {A₀ : Scheme.{0}} {f₀ : A₀ ⟶ Spec (CommRingCat.of S₀)} (L₀ : RelativeGroupLaw S₀ f₀)

    (act₀ : Λ → (A₀ ⟶ A₀)) (act₀_over : ∀ x : Λ, act₀ x ≫ f₀ = f₀)
    (act₀_hom : ∀ (x : Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S₀)) (P Q : SchemeHomOver t f₀),
      (L₀.mul t P Q).1 ≫ act₀ x =
        (L₀.mul t ⟨P.1 ≫ act₀ x, by rw [Category.assoc, act₀_over, P.2]⟩
          ⟨Q.1 ≫ act₀ x, by rw [Category.assoc, act₀_over, Q.2]⟩).1)
    (act₀_one : act₀ 1 = 𝟙 A₀)
    (act₀_mul : ∀ x y : Λ, act₀ (x * y) = act₀ y ≫ act₀ x)
    (act₀_add : ∀ (x y : Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S₀)) (P : SchemeHomOver t f₀),
      P.1 ≫ act₀ (x + y) =
        (L₀.mul t ⟨P.1 ≫ act₀ x, by rw [Category.assoc, act₀_over, P.2]⟩
          ⟨P.1 ≫ act₀ y, by rw [Category.assoc, act₀_over, P.2]⟩).1)
    (D₀ : BareDeformation f₀ L₀ S) :

    ∃ (jκ : (pullback D₀.f (specMap S (ResidueField S))) ⟶ A₀) (hjκ : jκ ≫ D₀.g = (pullback.fst D₀.f (specMap S (ResidueField S))))
      (ψ : Λ → ((pullback D₀.f (specMap S (ResidueField S))) ⟶ (pullback D₀.f (specMap S (ResidueField S)))))
      (hψ : ∀ x : Λ, ψ x ≫ (pullback.snd D₀.f (specMap S (ResidueField S))) = (pullback.snd D₀.f (specMap S (ResidueField S)))),
      (∀ x : Λ, ψ x ≫ jκ = jκ ≫ act₀ x) ∧
      (∀ (x : Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (ResidueField S))) (P Q : SchemeHomOver t (pullback.snd D₀.f (specMap S (ResidueField S)))),
        pushPt (ψ x) (hψ x) ((RelativeGroupLaw.baseChange (specMap S (ResidueField S)) D₀.L).mul t P Q) = (RelativeGroupLaw.baseChange (specMap S (ResidueField S)) D₀.L).mul t (pushPt (ψ x) (hψ x) P) (pushPt (ψ x) (hψ x) Q)) ∧
      ψ 1 = 𝟙 (pullback D₀.f (specMap S (ResidueField S))) ∧
      (∀ x y : Λ, ψ (x * y) = ψ y ≫ ψ x) ∧
      (∀ (x y : Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (ResidueField S))) (P : SchemeHomOver t (pullback.snd D₀.f (specMap S (ResidueField S)))),
        P.1 ≫ ψ (x + y) =
          ((RelativeGroupLaw.baseChange (specMap S (ResidueField S)) D₀.L).mul t ⟨P.1 ≫ ψ x, by rw [Category.assoc, hψ, P.2]⟩
            ⟨P.1 ≫ ψ y, by rw [Category.assoc, hψ, P.2]⟩).1) := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_BareDeformation_exists_specialFibre_act_comp_eq_of_act_bare.solution
