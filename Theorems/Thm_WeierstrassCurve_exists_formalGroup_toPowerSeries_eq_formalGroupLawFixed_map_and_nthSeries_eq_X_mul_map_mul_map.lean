import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_exists_formalGroup_toPowerSeries_eq_formalGroupLawFixed_map_and_nthSeries_eq_X_mul_map_mul_map
attribute [-simp] FormalGroup.DrinfeldLevel.mk.sizeOf_spec FormalGroup.DrinfeldLevel.mk.injEq FormalGroup.LawIso.mk.sizeOf_spec FormalGroup.LawHom.mk.sizeOf_spec FormalGroup.LawHom.mk.injEq FormalGroup.LawIso.mk.injEq

set_option autoImplicit false

open Polynomial

theorem WeierstrassCurve.exists_formalGroup_toPowerSeries_eq_formalGroupLawFixed_map_and_nthSeries_eq_X_mul_map_mul_map
    {S T : Type} [CommRing S] [CommRing T] (Φ : S →+* T)
    (V : WeierstrassCurve S) (FS : FormalGroup S) (hFS : FS.toPowerSeries = V.formalGroupLawFixed)
    (q : ℕ) (g : S[X]) (v : PowerSeries S)
    (hfacq : FS.nthSeries q = PowerSeries.X * (↑g : PowerSeries S) * v) :
    ∃ FT : FormalGroup T, FT.toPowerSeries = (V.map Φ).formalGroupLawFixed ∧
      FT.nthSeries q = PowerSeries.X * (↑(g.map Φ) : PowerSeries T) * PowerSeries.map Φ v := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_exists_formalGroup_toPowerSeries_eq_formalGroupLawFixed_map_and_nthSeries_eq_X_mul_map_mul_map.solution
