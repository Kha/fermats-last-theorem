import Definitions.Def_ModularCurve_LaurentCoeff
import P2M.Util
import P2M.Sol.S_ModularCurve_order_coeffMap

open ModularCurve

theorem ModularCurve.order_coeffMap {R S : Type*} [CommRing R] [CommRing S] {φ : R →+* S} (hφ : Function.Injective φ) (x : LaurentSeries R) : (coeffMap φ x).order = x.order := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_order_coeffMap.solution
