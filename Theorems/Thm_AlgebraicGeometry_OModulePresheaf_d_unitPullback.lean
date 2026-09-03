import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCochainPullback
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_d_unitPullback

set_option autoImplicit false

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

universe u
theorem AlgebraicGeometry.OModulePresheaf.d_unitPullback
    {R R' : Type u} [CommRing R] [CommRing R'] {X Y : Scheme.{u}}
    (πX : X ⟶ Spec (CommRingCat.of R')) (πY : Y ⟶ Spec (CommRingCat.of R))
    (h : X ⟶ Y) (𝒲 : X.OrderedAffineCover) (𝒦 : Y.OrderedAffineCover) (lam : 𝒲.ι → 𝒦.ι)
    (hlam : ∀ w, 𝒲.U w ≤ h ⁻¹ᵁ 𝒦.U (lam w)) (n : ℕ) (z : (OModulePresheaf.unit πY).cochain 𝒦 n) :
    (OModulePresheaf.unit πX).d 𝒲 n (OModulePresheaf.unitPullback (πX := πX) h 𝒲 𝒦 lam hlam n z) =
      OModulePresheaf.unitPullback (πX := πX) h 𝒲 𝒦 lam hlam (n + 1) ((OModulePresheaf.unit πY).d 𝒦 n z) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_d_unitPullback.solution
