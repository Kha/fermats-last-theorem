module

public import Definitions.Def_AlgebraicCurve_PlacesOverDVR
public import P2M.Util
public import P2M.Sol.S_AlgebraicCurve_Place_inertiaDeg_pos

@[expose] public section

open AlgebraicCurve
theorem AlgebraicCurve.Place.inertiaDeg_pos {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] [FiniteDimensional F F'] [Algebra.IsSeparable F F'] (w : Place K F') : 0 < w.inertiaDeg F := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Place_inertiaDeg_pos.solution
