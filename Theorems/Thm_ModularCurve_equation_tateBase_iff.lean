module

public import Definitions.Def_ModularCurve_TateSlots
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic
public import P2M.Util
public import P2M.Sol.S_ModularCurve_equation_tateBase_iff

@[expose] public section

open ModularCurve
theorem ModularCurve.equation_tateBase_iff (K : Type*) [CommRing K] (p : ℕ) [NeZero p] (x y : LaurentSeries K) : (tateBase K p).toAffine.Equation x y ↔ y ^ 2 + x * y = x ^ 3 + qExpand K p (laurentOfInt K tateA4) * x + qExpand K p (laurentOfInt K tateA6) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_equation_tateBase_iff.solution
