import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.Localization.Away.Basic
import Definitions.Def_AlgebraicGeometry_OModulePresheafIdealFiltration
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_supportedIn_idealPowQuot

open AlgebraicGeometry

universe u
theorem AlgebraicGeometry.OModulePresheaf.supportedIn_idealPowQuot {R : Type u} [CommRing R] {V : Scheme.{u}} (π : V ⟶ Spec (.of R)) (I : V.IdealSheafData) (F : OModulePresheaf π) (k : ℕ) {Y : TopologicalSpace.Closeds V} (hFs : F.SupportedIn Y) : (OModulePresheaf.idealPowQuot π I F k).SupportedIn Y := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_supportedIn_idealPowQuot.solution
