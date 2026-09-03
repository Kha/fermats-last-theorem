import Mathlib
import Definitions.Def_ModularCurve_UVCrossingModel
import P2M.Util
import P2M.Sol.S_ModularCurve_UVCrossingModel_exists_ringEquiv_adjoinRoot
set_option autoImplicit false

open ModularCurve
theorem ModularCurve.UVCrossingModel.exists_ringEquiv_adjoinRoot {W : Type*} [CommRing W] (c : W) :
    ∃ e : UVCrossingModel W c ≃+*
        AdjoinRoot (Polynomial.X ^ 2 -
          Polynomial.C (PowerSeries.X : PowerSeries (PowerSeries W ⧸
            Ideal.span {(PowerSeries.X : PowerSeries W) - PowerSeries.C c})) * Polynomial.X +
          Polynomial.C (PowerSeries.C (Ideal.Quotient.mk
            (Ideal.span {(PowerSeries.X : PowerSeries W) - PowerSeries.C c}) (PowerSeries.C c)))),
      e (U c) = AdjoinRoot.root _ ∧
      e (S c) = AdjoinRoot.of _ PowerSeries.X ∧
      ∀ w : W, e (const c w) = AdjoinRoot.of _ (PowerSeries.C (Ideal.Quotient.mk
            (Ideal.span {(PowerSeries.X : PowerSeries W) - PowerSeries.C c}) (PowerSeries.C w))) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_UVCrossingModel_exists_ringEquiv_adjoinRoot.solution
