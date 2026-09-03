import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_GaloisRep_Flat
import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Basic
import P2M.Util
import P2M.Sol.S_WeierstrassProjModel_toProjective_isElliptic_map_of_isGoodPrimeFor

open WeierstrassCurve GaloisRep

theorem WeierstrassProjModel.toProjective_isElliptic_map_of_isGoodPrimeFor
    (W : WeierstrassCurve ℤ) (p : ℕ) [Fact p.Prime] (hgood : W.IsGoodPrimeFor p) :
    (W.map (algebraMap ℤ (ratLocalizedAt p))).toProjective.IsElliptic := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassProjModel_toProjective_isElliptic_map_of_isGoodPrimeFor.solution
