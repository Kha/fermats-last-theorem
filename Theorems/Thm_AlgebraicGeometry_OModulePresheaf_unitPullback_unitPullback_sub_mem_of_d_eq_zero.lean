import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCechCup
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCochainPullback
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCechOrdered
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_unitPullback_unitPullback_sub_mem_of_d_eq_zero

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.OModulePresheaf.unitPullback_unitPullback_sub_mem_of_d_eq_zero
    {R R' R'' : Type u} [CommRing R] [CommRing R'] [CommRing R''] {X Y Z : Scheme.{u}}
    (πX : X ⟶ Spec (CommRingCat.of R'')) (πY : Y ⟶ Spec (CommRingCat.of R')) (πZ : Z ⟶ Spec (CommRingCat.of R))
    (h : X ⟶ Y) (h' : Y ⟶ Z) (h'' : X ⟶ Z) (hh : h'' = h ≫ h')
    (𝒲 : X.OrderedAffineCover) (𝒦 : Y.OrderedAffineCover) (𝒦' : Z.OrderedAffineCover)
    (lam : 𝒲.ι → 𝒦.ι) (lam' : 𝒦.ι → 𝒦'.ι) (lam'' : 𝒲.ι → 𝒦'.ι) (hlc : lam'' = lam' ∘ lam)
    (hlam : ∀ w, 𝒲.U w ≤ h ⁻¹ᵁ 𝒦.U (lam w)) (hlam' : ∀ i, 𝒦.U i ≤ h' ⁻¹ᵁ 𝒦'.U (lam' i))
    (hlam'' : ∀ w, 𝒲.U w ≤ h'' ⁻¹ᵁ 𝒦'.U (lam'' w))
    (n : ℕ) (z : (OModulePresheaf.unit πZ).cochain 𝒦' n) (hz : (OModulePresheaf.unit πZ).d 𝒦' n z = 0) :
    OModulePresheaf.unitPullback (πX := πX) h 𝒲 𝒦 lam hlam n (OModulePresheaf.unitPullback (πX := πY) h' 𝒦 𝒦' lam' hlam' n z) -
        OModulePresheaf.unitPullback (πX := πX) h'' 𝒲 𝒦' lam'' hlam'' n z
      ∈ (show Submodule R'' ((OModulePresheaf.unit πX).cochain 𝒲 n) from
          match n with
          | 0 => ⊥
          | m + 1 => LinearMap.range ((OModulePresheaf.unit πX).d 𝒲 m)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_unitPullback_unitPullback_sub_mem_of_d_eq_zero.solution
