import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCochainPullback
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_unitPullback_comap_id_apply

set_option autoImplicit false

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

universe u
theorem AlgebraicGeometry.OModulePresheaf.unitPullback_comap_id_apply
    {R R' : Type u} [CommRing R] [CommRing R'] {X Y : Scheme.{u}}
    (πX : X ⟶ Spec (CommRingCat.of R')) (πY : Y ⟶ Spec (CommRingCat.of R))
    (h : X ⟶ Y) [IsAffineHom h] (𝒦 : Y.OrderedAffineCover)
    (hlam : ∀ w : (𝒦.comap h).ι, (𝒦.comap h).U w ≤ h ⁻¹ᵁ 𝒦.U w)
    (n : ℕ) (z : (OModulePresheaf.unit πY).cochain 𝒦 n) (s : (𝒦.comap h).Idx n) :
    OModulePresheaf.unitPullback (πX := πX) h (𝒦.comap h) 𝒦 (fun w => w) hlam n z s =
      (X.presheaf.map (homOfLE (𝒦.comap_inter_le h s)).op).hom ((h.app (𝒦.inter s)).hom (z s)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_unitPullback_comap_id_apply.solution
