import Definitions.Def_CerednikDrinfeld_QMModuli
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_QM_FakeEllipticCurve_forall_mapPt_eq_one_of_forall_rationalPoint
attribute [-instance] GoodReductionJacobian.RelativeGroupLaw.isIso_endKerStr_schemeHomOverId
attribute [-simp] GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ NeronModelInfra.schemeHomOverNpow_succ NeronModelInfra.schemeHomOverNpow_zero NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe

set_option autoImplicit false

universe u

p2m_open "CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld CerednikDrinfeld.QM~exists_comp_eq_of_forall_factorsThrough_of_isReduced"
open scoped Quaternion

theorem CerednikDrinfeld.QM.FakeEllipticCurve.forall_mapPt_eq_one_of_forall_rationalPoint
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    (k : Type u) [Field k] [IsAlgClosed k]
    (E E' E'' : FakeEllipticCurve Λ N k) (n : ℕ) (hnk : (n : k) ≠ 0)
    (φ' : E.A ⟶ E'.A) (hφ' : φ' ≫ E'.f = E.f)
    (hφ'mul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t E.f),
      mapPt φ' hφ' (E.L.mul t P Q) = E'.L.mul t (mapPt φ' hφ' P) (mapPt φ' hφ' Q))
    (hφ'act : ∀ x : ↥Λ, E.act x ≫ φ' = φ' ≫ E'.act x)
    (ψ' : E'.A ⟶ E.A) (hψ' : ψ' ≫ E.f = E'.f)
    (hψ'φ' : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t E.f),
      mapPt ψ' hψ' (mapPt φ' hφ' P) = nsmulPt E.L t n P)
    (hφ'ψ' : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (Q : SchemeHomOver t E'.f),
      mapPt φ' hφ' (mapPt ψ' hψ' Q) = nsmulPt E'.L t n Q)
    (φ'' : E.A ⟶ E''.A) (hφ'' : φ'' ≫ E''.f = E.f)
    (hpts : ∀ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E.f,
      mapPt φ' hφ' P = E'.L.one _ → mapPt φ'' hφ'' P = E''.L.one _) :
    ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t E.f),
      mapPt φ' hφ' P = E'.L.one t → mapPt φ'' hφ'' P = E''.L.one t := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_forall_mapPt_eq_one_of_forall_rationalPoint.solution
