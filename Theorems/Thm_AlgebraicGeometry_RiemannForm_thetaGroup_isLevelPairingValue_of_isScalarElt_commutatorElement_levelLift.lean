import Mathlib
import Definitions.Def_AlgebraicGeometry_RiemannForm
import Definitions.Def_AlgebraicGeometry_ThetaGroup
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_RiemannForm_thetaGroup_isLevelPairingValue_of_isScalarElt_commutatorElement_levelLift

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.RiemannForm
open scoped commutatorElement

theorem AlgebraicGeometry.RiemannForm.thetaGroup.isLevelPairingValue_of_isScalarElt_commutatorElement_levelLift
    (k : Type) [Field k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative) (𝓛 : A.Modules) (n : ℕ) (P : L.AlgPoints hc k)
    (hx : translation f L (RelativeGroupLaw.AlgPoints.toPoint P) ≫ L.schemeNsmul n = L.schemeNsmul n) (c : k) :
    (∀ g : thetaGroup f L hc ((Scheme.Modules.pullback (L.schemeNsmul n)).obj 𝓛),
      thetaGroup.IsScalarElt f L hc _ ⁅levelLift f L hc 𝓛 n P hx, g⁆ c →
        IsLevelPairingValue f L 𝓛 n (RelativeGroupLaw.AlgPoints.toPoint P)
          (RelativeGroupLaw.AlgPoints.toPoint (n • Multiplicative.toAdd (thetaGroup.pt f L hc _ g))) c) ∧
    (∀ Q₁ : L.AlgPoints hc k,
      IsLevelPairingValue f L 𝓛 n (RelativeGroupLaw.AlgPoints.toPoint P) (RelativeGroupLaw.AlgPoints.toPoint (n • Q₁)) c →
        ∃ g : thetaGroup f L hc ((Scheme.Modules.pullback (L.schemeNsmul n)).obj 𝓛),
          thetaGroup.pt f L hc _ g = Multiplicative.ofAdd Q₁ ∧
            thetaGroup.IsScalarElt f L hc _ ⁅levelLift f L hc 𝓛 n P hx, g⁆ c) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_RiemannForm_thetaGroup_isLevelPairingValue_of_isScalarElt_commutatorElement_levelLift.solution
