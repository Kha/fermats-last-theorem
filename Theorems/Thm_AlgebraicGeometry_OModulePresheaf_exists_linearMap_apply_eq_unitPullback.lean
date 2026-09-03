import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCochainPullback
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_linearMap_apply_eq_unitPullback

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.OModulePresheaf.exists_linearMap_apply_eq_unitPullback
    {R : Type u} [CommRing R] {X Y : Scheme.{u}}
    (πX : X ⟶ Spec (CommRingCat.of R)) (πY : Y ⟶ Spec (CommRingCat.of R))
    (h : X ⟶ Y) (hh : h ≫ πY = πX)
    (𝒲 : X.OrderedAffineCover) (𝒦 : Y.OrderedAffineCover) (lam : 𝒲.ι → 𝒦.ι)
    (hlam : ∀ w, 𝒲.U w ≤ h ⁻¹ᵁ 𝒦.U (lam w)) (n : ℕ) :
    ∃ L : (OModulePresheaf.unit πY).cochain 𝒦 n →ₗ[R] (OModulePresheaf.unit πX).cochain 𝒲 n,
      ∀ z, L z = OModulePresheaf.unitPullback (πX := πX) h 𝒲 𝒦 lam hlam n z := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_linearMap_apply_eq_unitPullback.solution
