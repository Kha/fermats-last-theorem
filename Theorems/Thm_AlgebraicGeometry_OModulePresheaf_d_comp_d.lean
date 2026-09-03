import Mathlib.AlgebraicGeometry.AffineScheme
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_d_comp_d

open AlgebraicGeometry

universe u
theorem AlgebraicGeometry.OModulePresheaf.d_comp_d {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)} (F : OModulePresheaf π) (K : V.OrderedAffineCover) (i : ℕ) : F.d K (i + 1) ∘ₗ F.d K i = 0 := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_d_comp_d.solution
