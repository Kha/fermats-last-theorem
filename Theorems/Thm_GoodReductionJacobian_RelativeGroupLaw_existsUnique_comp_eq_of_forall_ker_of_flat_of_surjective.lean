import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_existsUnique_comp_eq_of_forall_ker_of_flat_of_surjective
attribute [-simp] GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left

set_option autoImplicit false

universe u

p2m_open "CategoryTheory AlgebraicGeometry~exists_isMonHom_comp_eq_of_forall_comp_eq_one_of_flat_of_surjective NeronModelInfra GoodReductionJacobian"

theorem GoodReductionJacobian.RelativeGroupLaw.existsUnique_comp_eq_of_forall_ker_of_flat_of_surjective
    {R : Type u} [CommRing R] {A B C : Scheme.{u}}
    {fA : A ⟶ Spec (CommRingCat.of R)} {fB : B ⟶ Spec (CommRingCat.of R)} {fC : C ⟶ Spec (CommRingCat.of R)}
    (LA : RelativeGroupLaw R fA) (LB : RelativeGroupLaw R fB) (LC : RelativeGroupLaw R fC)
    (p : A ⟶ B) (hp : p ≫ fB = fA) [Flat p] [Surjective p] [QuasiCompact p]
    (p_hom : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t fA),
      (⟨(LA.mul t P Q).1 ≫ p, by rw [Category.assoc, hp]; exact (LA.mul t P Q).2⟩ : SchemeHomOver t fB) =
        LB.mul t ⟨P.1 ≫ p, by rw [Category.assoc, hp]; exact P.2⟩ ⟨Q.1 ≫ p, by rw [Category.assoc, hp]; exact Q.2⟩)
    (g : A ⟶ C) (hg : g ≫ fC = fA)
    (g_hom : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t fA),
      (⟨(LA.mul t P Q).1 ≫ g, by rw [Category.assoc, hg]; exact (LA.mul t P Q).2⟩ : SchemeHomOver t fC) =
        LC.mul t ⟨P.1 ≫ g, by rw [Category.assoc, hg]; exact P.2⟩ ⟨Q.1 ≫ g, by rw [Category.assoc, hg]; exact Q.2⟩)
    (hker : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (P : SchemeHomOver t fA),
      (⟨P.1 ≫ p, by rw [Category.assoc, hp]; exact P.2⟩ : SchemeHomOver t fB) = LB.one t →
      (⟨P.1 ≫ g, by rw [Category.assoc, hg]; exact P.2⟩ : SchemeHomOver t fC) = LC.one t) :
    ∃ h : B ⟶ C, p ≫ h = g ∧
      (∃ hh : h ≫ fC = fB,
        ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t fB),
          (⟨(LB.mul t P Q).1 ≫ h, by rw [Category.assoc, hh]; exact (LB.mul t P Q).2⟩ : SchemeHomOver t fC) =
            LC.mul t ⟨P.1 ≫ h, by rw [Category.assoc, hh]; exact P.2⟩ ⟨Q.1 ≫ h, by rw [Category.assoc, hh]; exact Q.2⟩) ∧
      ∀ h' : B ⟶ C, p ≫ h' = g → h' = h := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_existsUnique_comp_eq_of_forall_ker_of_flat_of_surjective.solution
