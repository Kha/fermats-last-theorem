import Mathlib
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_WeierstrassCurve_FormalGroup
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_exists_genericPoint_formalGroupLawFixed_eq_add

set_option autoImplicit false

open WeierstrassCurve

open Classical in

theorem WeierstrassCurve.exists_genericPoint_formalGroupLawFixed_eq_add
    {R : Type} [CommRing R] [IsDomain R] (W : WeierstrassCurve R) [W.IsElliptic] :
    ∃ (hwF : WeierstrassCurve.genι (W.fgGenW W.formalGroupLawFixed) ≠ 0)
      (hw0 : WeierstrassCurve.genι (W.fgGenW (MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) R)) ≠ 0)
      (hw1 : WeierstrassCurve.genι (W.fgGenW (MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) R)) ≠ 0),
      W.genericPoint (PowerSeries.HasSubst.of_constantCoeff_zero W.constantCoeff_formalGroupLawFixed) hwF
        = W.genericPoint (PowerSeries.HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X 0)) hw0
          + W.genericPoint (PowerSeries.HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X 1)) hw1 := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_exists_genericPoint_formalGroupLawFixed_eq_add.solution
