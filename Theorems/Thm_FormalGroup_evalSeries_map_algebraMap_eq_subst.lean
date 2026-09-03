import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import P2M.Util
import P2M.Sol.S_FormalGroup_evalSeries_map_algebraMap_eq_subst

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel
  WeierstrassCurve.DrinfeldGlobal IsLocalRing HomogeneousLocalization

attribute [local instance] MvPolynomial.gradedAlgebra

theorem FormalGroup.evalSeries_map_algebraMap_eq_subst
    {T : Type} [CommRing T] [IsLocalRing T] [IsNoetherianRing T] [IsAdicComplete (maximalIdeal T) T]
    (g s : PowerSeries T) (hs : PowerSeries.constantCoeff s = 0) :
    (letI : WithIdeal (PowerSeries T) := ⟨maximalIdeal (PowerSeries T)⟩;
      FormalGroup.evalSeries (PowerSeries.map (algebraMap T (PowerSeries T)) g) s) = PowerSeries.subst s g := by p2m_exact_reverting @_root_.P2MW.S_FormalGroup_evalSeries_map_algebraMap_eq_subst.solution
