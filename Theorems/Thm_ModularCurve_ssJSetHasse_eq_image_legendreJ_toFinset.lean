module

public import Mathlib
public import Definitions.Def_WeierstrassCurve_HasseInvariant
public import Definitions.Def_Polynomial_DeuringPolynomial
public import Definitions.Def_ModularCurve_LegendreJ
public import P2M.Util
public import P2M.Sol.S_ModularCurve_ssJSetHasse_eq_image_legendreJ_toFinset

@[expose] public section

open Polynomial ModularCurve
theorem ModularCurve.ssJSetHasse_eq_image_legendreJ_toFinset (q : ℕ) [Fact q.Prime] (hq : q ≠ 2) (K : Type*)
    [Field K] [IsAlgClosed K] [CharP K q] [DecidableEq K] :
    ssJSetHasse q K
      = legendreJ '' ↑(((Polynomial.deuringPolynomial q).map (Int.castRingHom K)).roots.toFinset) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_ssJSetHasse_eq_image_legendreJ_toFinset.solution
