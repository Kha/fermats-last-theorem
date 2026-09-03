import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCochainPullback
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_map_app_unitPullback_eq_unitPullback_comp

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

universe u

theorem AlgebraicGeometry.OModulePresheaf.map_app_unitPullback_eq_unitPullback_comp
    {R R' R'' : Type u} [CommRing R] [CommRing R'] [CommRing R''] {X X' Y : Scheme.{u}}
    (πX : X ⟶ Spec (CommRingCat.of R')) (πX' : X' ⟶ Spec (CommRingCat.of R'')) (πY : Y ⟶ Spec (CommRingCat.of R))
    (h : X ⟶ Y) (g : X' ⟶ X) [IsAffineHom g]
    (𝒲 : X.OrderedAffineCover) (𝒦 : Y.OrderedAffineCover) (lam : 𝒲.ι → 𝒦.ι)
    (hlam : ∀ w, 𝒲.U w ≤ h ⁻¹ᵁ 𝒦.U (lam w))
    (hlam' : ∀ w : (𝒲.comap g).ι, (𝒲.comap g).U w ≤ (g ≫ h) ⁻¹ᵁ 𝒦.U (lam w))
    (n : ℕ) (z : (OModulePresheaf.unit πY).cochain 𝒦 n) (s : (𝒲.comap g).Idx n) :
    (X'.presheaf.map (homOfLE (𝒲.comap_inter_le g s)).op).hom
        ((g.app (𝒲.inter s)).hom (OModulePresheaf.unitPullback (πX := πX) h 𝒲 𝒦 lam hlam n z s))
      = OModulePresheaf.unitPullback (πX := πX') (g ≫ h) (𝒲.comap g) 𝒦 lam hlam' n z s := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_map_app_unitPullback_eq_unitPullback_comp.solution
