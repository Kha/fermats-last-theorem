import Mathlib
import Definitions.Def_AlgebraicGeometry_RiemannForm
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_ThetaGroup
import Definitions.Def_CerednikDrinfeld_QMModuli
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_RiemannForm_thetaGroup_exists_monoidHom_pullback_pt_eq_and_isScalarElt

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.RiemannForm

theorem AlgebraicGeometry.RiemannForm.thetaGroup.exists_monoidHom_pullback_pt_eq_and_isScalarElt
    (k : Type) [Field k] {A B : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k)) (g : B ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative) (LB : RelativeGroupLaw k g) (hcB : LB.IsCommutative)
    (φ : A ⟶ B) (hφ : φ ≫ g = f)
    (hφhom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t f),
      CerednikDrinfeld.QM.mapPt φ hφ (L.mul t P Q) = LB.mul t (CerednikDrinfeld.QM.mapPt φ hφ P) (CerednikDrinfeld.QM.mapPt φ hφ Q))
    (φpt : Multiplicative (L.AlgPoints hc k) →* Multiplicative (LB.AlgPoints hcB k))
    (hφpt : ∀ z : Multiplicative (L.AlgPoints hc k),
      RelativeGroupLaw.AlgPoints.toPoint (Multiplicative.toAdd (φpt z)) =
        CerednikDrinfeld.QM.mapPt φ hφ (RelativeGroupLaw.AlgPoints.toPoint (Multiplicative.toAdd z)))
    (M : B.Modules) :
    ∃ Ψ : MonoidHom.eqLocus
          ((thetaGroup.pt g LB hcB M).comp (MonoidHom.fst (thetaGroup g LB hcB M) (Multiplicative (L.AlgPoints hc k))))
          (φpt.comp (MonoidHom.snd (thetaGroup g LB hcB M) (Multiplicative (L.AlgPoints hc k)))) →*
        thetaGroup f L hc ((Scheme.Modules.pullback φ).obj M),
      (∀ p, thetaGroup.pt f L hc ((Scheme.Modules.pullback φ).obj M) (Ψ p) = p.1.2) ∧
      (∀ p (c : k), thetaGroup.IsScalarElt g LB hcB M p.1.1 c → p.1.2 = 1 →
        thetaGroup.IsScalarElt f L hc ((Scheme.Modules.pullback φ).obj M) (Ψ p) c) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_RiemannForm_thetaGroup_exists_monoidHom_pullback_pt_eq_and_isScalarElt.solution
