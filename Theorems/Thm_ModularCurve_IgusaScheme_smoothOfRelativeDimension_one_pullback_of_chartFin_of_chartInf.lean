import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_ModularCurve_ReductionModL
import Definitions.Def_ModularCurve_ReductionOfPointsAgreesModL
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_ModularCurve_FibreModel
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_ModularCurve_IgusaScheme
import P2M.Util
import P2M.Sol.S_ModularCurve_IgusaScheme_smoothOfRelativeDimension_one_pullback_of_chartFin_of_chartInf

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  ModularCurve AlgebraicCurve IsLocalRing ModularCurve.IgusaScheme
set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.IgusaScheme.smoothOfRelativeDimension_one_pullback_of_chartFin_of_chartInf
    (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime]
    (k : Type) [Field k] (φ : ↥(GaloisRep.ratLocalizedAt ℓ) →+* k)
    (hFin : SmoothOfRelativeDimension 1
      (pullback.snd
        (Spec.map (CommRingCat.ofHom
          (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) ↥(chartAlgFin N ℓ))))
        (Spec.map (CommRingCat.ofHom φ))))
    (hInf : SmoothOfRelativeDimension 1
      (pullback.snd
        (Spec.map (CommRingCat.ofHom
          (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) ↥(chartAlgInf N ℓ))))
        (Spec.map (CommRingCat.ofHom φ)))) :
    SmoothOfRelativeDimension 1
      (pullback.snd (igusaTo N ℓ) (Spec.map (CommRingCat.ofHom φ))) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_IgusaScheme_smoothOfRelativeDimension_one_pullback_of_chartFin_of_chartInf.solution
