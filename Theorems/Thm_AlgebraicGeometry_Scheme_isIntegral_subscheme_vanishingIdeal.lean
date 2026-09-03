import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.Properties
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_isIntegral_subscheme_vanishingIdeal

open AlgebraicGeometry TopologicalSpace

universe u
theorem AlgebraicGeometry.Scheme.isIntegral_subscheme_vanishingIdeal {V : Scheme.{u}} (Z : Closeds V) (hZ : IsIrreducible (Z : Set V)) : IsIntegral (Scheme.IdealSheafData.vanishingIdeal Z).subscheme := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_isIntegral_subscheme_vanishingIdeal.solution
