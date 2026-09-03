import Mathlib
import Definitions.Def_CerednikDrinfeld_QMModuli
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_hom_mapPt_eq_of_forall_curve_eq_mapPt_of_isAlgClosed
attribute [-simp] GoodReductionJacobian.prodInr_comp_prodFst GoodReductionJacobian.RelativeGroupLaw.prod_inv GoodReductionJacobian.prodInl_comp_prodSnd GoodReductionJacobian.prodInr_comp_prodSnd GoodReductionJacobian.prodInl_comp_prodFst GoodReductionJacobian.prodFstPt_prodPairPt GoodReductionJacobian.prodFst_coe GoodReductionJacobian.prodSndPt_prodPairPt GoodReductionJacobian.RelativeGroupLaw.prod_one GoodReductionJacobian.prodPairPt_coe GoodReductionJacobian.prodPairPt_prodFstPt_prodSndPt GoodReductionJacobian.prodFstPt_coe GoodReductionJacobian.RelativeGroupLaw.prod_mul GoodReductionJacobian.prodSndPt_coe GoodReductionJacobian.prodSnd_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left RegularLocalRingQuotientAscent.dualNumberFst_apply

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld.QM
theorem GoodReductionJacobian.AbelianSchemePropertyBundle.exists_hom_mapPt_eq_of_forall_curve_eq_mapPt_of_isAlgClosed
    (k : Type) [Field k] [IsAlgClosed k] [CharZero k]
    {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k)) (L : RelativeGroupLaw k f)
    (hA : AbelianSchemePropertyBundle k f)
    {A' : Scheme.{0}} (f' : A' ⟶ Spec (CommRingCat.of k)) (L' : RelativeGroupLaw k f')
    (hA' : AbelianSchemePropertyBundle k f')

    (h : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f → SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f')
    (hh : ∀ P Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f,
      h (L.mul (𝟙 (Spec (CommRingCat.of k))) P Q) = L'.mul (𝟙 (Spec (CommRingCat.of k))) (h P) (h Q))

    {n : ℕ} (C : Fin n → Scheme.{0}) (c : ∀ i : Fin n, C i ⟶ Spec (CommRingCat.of k))
    (ν : ∀ i : Fin n, C i ⟶ A) (hν : ∀ i : Fin n, ν i ≫ f = c i)
    (hC : ∀ i : Fin n, IsProper (c i) ∧ SmoothOfRelativeDimension 1 (c i) ∧ IsIntegral (C i))
    (hsurj : ∀ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f,
      ∃ y : ∀ i : Fin n, SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) (c i),
        (List.ofFn (fun i : Fin n => mapPt (ν i) (hν i) (y i))).foldr
            (fun Q R => L.mul (𝟙 (Spec (CommRingCat.of k))) Q R)
            (L.one (𝟙 (Spec (CommRingCat.of k)))) = P)

    (w : ∀ i : Fin n, C i ⟶ A') (hw : ∀ i : Fin n, w i ≫ f' = c i)
    (hhw : ∀ (i : Fin n) (y : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) (c i)),
      h (mapPt (ν i) (hν i) y) = mapPt (w i) (hw i) y) :
    ∃ (u : A ⟶ A') (hu : u ≫ f' = f),
      ∀ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f, mapPt u hu P = h P := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_hom_mapPt_eq_of_forall_curve_eq_mapPt_of_isAlgClosed.solution
