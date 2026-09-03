import Mathlib
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_EllipticCurve_ZeroComponentAt
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_mem_valuationSubring_of_equation

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point
theorem WeierstrassCurve.mem_valuationSubring_of_equation {K : Type*} [Field K] [Algebra ℚ K] (W : WeierstrassCurve ℤ) (A : ValuationSubring K) {x y : K} (h : ((W.map (Int.castRingHom ℚ))⁄K).toAffine.Equation x y) (hx : x ∈ A) : y ∈ A := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_mem_valuationSubring_of_equation.solution
