import Mathlib
import Definitions.Def_ModularCurve_UVCrossingModel
import Definitions.Def_ModularCurve_UVCrossingChart
import P2M.Util
import P2M.Sol.S_ModularCurve_UVCrossingModel_exists_ringEquiv_adjoinRoot_of_isPrecomplete
set_option autoImplicit false

open ModularCurve
theorem ModularCurve.UVCrossingModel.exists_ringEquiv_adjoinRoot_of_isPrecomplete {W : Type*} [CommRing W]
    [IsNoetherianRing W] [IsLocalRing W] [IsDomain W]
    (c : W) (hc0 : c ≠ 0) (hcu : ¬IsUnit c) [IsPrecomplete (Ideal.span {c}) W] :
    ∃ e : UVCrossingModel W c ≃+*
        AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C (PowerSeries.X : PowerSeries W) * Polynomial.X +
          Polynomial.C (PowerSeries.C c)),
      e (U c) = AdjoinRoot.root _ ∧
      ∀ f : PowerSeries W, e (chartHom c f) = AdjoinRoot.of _ f := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_UVCrossingModel_exists_ringEquiv_adjoinRoot_of_isPrecomplete.solution
