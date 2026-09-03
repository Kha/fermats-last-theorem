import Mathlib
import Definitions.Def_AlgebraicGeometry_RiemannForm
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_ThetaGroup
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_RiemannForm_thetaGroup_exists_iso_pullback_translation_of_injOn_pt_of_range_pt_eq_torsion

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.RiemannForm

theorem AlgebraicGeometry.RiemannForm.thetaGroup.exists_iso_pullback_translation_of_injOn_pt_of_range_pt_eq_torsion
    (k : Type) [Field k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative) (M : A.Modules) (n : ℕ)
    (K : Subgroup (thetaGroup f L hc M))
    (hKinj : ∀ g ∈ K, ∀ h ∈ K, thetaGroup.pt f L hc M g = thetaGroup.pt f L hc M h → g = h)
    (hKpt : ∀ Q : L.AlgPoints hc k, (∃ g ∈ K, thetaGroup.pt f L hc M g = Multiplicative.ofAdd Q) ↔ n • Q = 0) :
    ∃ ψ : ∀ P : L.AlgPoints hc k, n • P = 0 →
        (M ≅ (Scheme.Modules.pullback (translation f L (RelativeGroupLaw.AlgPoints.toPoint P))).obj M),
      (∀ h0 : n • (0 : L.AlgPoints hc k) = 0,
        ψ 0 h0 = ((Scheme.Modules.pullbackId A).app M).symm ≪≫
          ((Scheme.Modules.pullbackCongr (translation_toPoint_zero f L hc)).app M).symm) ∧
      (∀ (P Q : L.AlgPoints hc k) (hP : n • P = 0) (hQ : n • Q = 0) (hPQ : n • (P + Q) = 0),
        ψ (P + Q) hPQ =
          ψ P hP ≪≫
            (Scheme.Modules.pullback (translation f L (RelativeGroupLaw.AlgPoints.toPoint P))).mapIso (ψ Q hQ) ≪≫
            (Scheme.Modules.pullbackComp (translation f L (RelativeGroupLaw.AlgPoints.toPoint P))
              (translation f L (RelativeGroupLaw.AlgPoints.toPoint Q))).app M ≪≫
            ((Scheme.Modules.pullbackCongr (translation_toPoint_add f L hc P Q)).app M).symm) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_RiemannForm_thetaGroup_exists_iso_pullback_translation_of_injOn_pt_of_range_pt_eq_torsion.solution
