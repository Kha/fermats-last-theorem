import Definitions.Def_CerednikDrinfeld_QMModuli
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_existsUnique_comp_eq_of_forall_mapPt_eq_one_of_flat_of_surjective
attribute [-simp] GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left

set_option autoImplicit false

universe u

p2m_open "CategoryTheory AlgebraicGeometry~exists_isMonHom_comp_eq_of_forall_comp_eq_one_of_flat_of_surjective NeronModelInfra GoodReductionJacobian CerednikDrinfeld.QM"

theorem GoodReductionJacobian.RelativeGroupLaw.existsUnique_comp_eq_of_forall_mapPt_eq_one_of_flat_of_surjective
    (R : Type u) [CommRing R] {D E X : Scheme.{u}}
    {gD : D ⟶ Spec (CommRingCat.of R)} {gE : E ⟶ Spec (CommRingCat.of R)} {gX : X ⟶ Spec (CommRingCat.of R)}
    (LD : RelativeGroupLaw R gD) (LE : RelativeGroupLaw R gE) (LX : RelativeGroupLaw R gX)
    (ψ : D ⟶ E) (hψ : ψ ≫ gE = gD)
    (ψ_hom : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t gD),
      mapPt ψ hψ (LD.mul t P Q) = LE.mul t (mapPt ψ hψ P) (mapPt ψ hψ Q))
    [Flat ψ] [Surjective ψ] [QuasiCompact ψ]
    (χ : D ⟶ X) (hχ : χ ≫ gX = gD)
    (χ_hom : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t gD),
      mapPt χ hχ (LD.mul t P Q) = LX.mul t (mapPt χ hχ P) (mapPt χ hχ Q))
    (hker : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (P : SchemeHomOver t gD),
      mapPt ψ hψ P = LE.one t → mapPt χ hχ P = LX.one t) :
    ∃ χ' : SchemeHomOver gE gX, ψ ≫ χ'.1 = χ ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (v w : SchemeHomOver t gE),
        mapPt χ'.1 χ'.2 (LE.mul t v w) = LX.mul t (mapPt χ'.1 χ'.2 v) (mapPt χ'.1 χ'.2 w)) ∧
      ∀ χ'' : SchemeHomOver gE gX, ψ ≫ χ''.1 = χ → χ'' = χ' := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_existsUnique_comp_eq_of_forall_mapPt_eq_one_of_flat_of_surjective.solution
