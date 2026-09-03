import Mathlib
import Definitions.Def_CerednikDrinfeld_QMModuli
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_isClosedImmersion_one_and_levelOne_axioms_of_isSeparated

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld.QM

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.isClosedImmersion_one_and_levelOne_axioms_of_isSeparated
    {S : Type u} [CommRing S] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of S)) [IsSeparated f]
    (L : RelativeGroupLaw S f) {ι : Type u} (act : ι → (A ⟶ A)) (act_over : ∀ i : ι, act i ≫ f = f)
    (act_hom : ∀ (i : ι) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t f),
      pushPt (act i) (act_over i) (L.mul t P Q) = L.mul t (pushPt (act i) (act_over i) P) (pushPt (act i) (act_over i) Q)) :
    IsClosedImmersion (L.one (𝟙 (Spec (CommRingCat.of S)))).1 ∧
    (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t f),
      FactorsThrough (L.one (𝟙 (Spec (CommRingCat.of S)))).1 P → FactorsThrough (L.one (𝟙 (Spec (CommRingCat.of S)))).1 Q →
        FactorsThrough (L.one (𝟙 (Spec (CommRingCat.of S)))).1 (L.mul t P Q) ∧
        FactorsThrough (L.one (𝟙 (Spec (CommRingCat.of S)))).1 (L.inv t P)) ∧
    (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)), FactorsThrough (L.one (𝟙 (Spec (CommRingCat.of S)))).1 (L.one t)) ∧
    (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t f),
      FactorsThrough (L.one (𝟙 (Spec (CommRingCat.of S)))).1 P → nsmulPt L t 1 P = L.one t) ∧
    (∀ (i : ι) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t f),
      FactorsThrough (L.one (𝟙 (Spec (CommRingCat.of S)))).1 P →
        FactorsThrough (L.one (𝟙 (Spec (CommRingCat.of S)))).1 (pushPt (act i) (act_over i) P)) ∧
    IsFinite ((L.one (𝟙 (Spec (CommRingCat.of S)))).1 ≫ f) ∧
    Flat ((L.one (𝟙 (Spec (CommRingCat.of S)))).1 ≫ f) ∧
    LocallyOfFinitePresentation ((L.one (𝟙 (Spec (CommRingCat.of S)))).1 ≫ f) ∧
    (∀ s : ↥(Spec (CommRingCat.of S)), ((L.one (𝟙 (Spec (CommRingCat.of S)))).1 ≫ f).finrank s = 1 ^ 2) ∧
    (∀ (k : Type u) [Field k] [IsAlgClosed k] (sk : S →+* k), ((1 : ℕ) : k) ≠ 0 →
      ∃ e : ZMod 1 × ZMod 1 ≃ {P : SchemeHomOver (geomPoint k sk) f // FactorsThrough (L.one (𝟙 (Spec (CommRingCat.of S)))).1 P},
        ∀ x y : ZMod 1 × ZMod 1,
          (e (x + y) : SchemeHomOver (geomPoint k sk) f) = L.mul (geomPoint k sk) (e x) (e y)) := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_isClosedImmersion_one_and_levelOne_axioms_of_isSeparated.solution
