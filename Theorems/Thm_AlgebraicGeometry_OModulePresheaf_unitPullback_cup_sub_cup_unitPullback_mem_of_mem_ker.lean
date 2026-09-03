import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCechCup
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCochainPullback
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_unitPullback_cup_sub_cup_unitPullback_mem_of_mem_ker
attribute [-instance] AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableOSub

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.OModulePresheaf.unitPullback_cup_sub_cup_unitPullback_mem_of_mem_ker
    {R R' : Type u} [CommRing R] [CommRing R'] {X Y : Scheme.{u}}
    (πX : X ⟶ Spec (CommRingCat.of R')) (πY : Y ⟶ Spec (CommRingCat.of R))
    (h : X ⟶ Y) (𝒲 : X.OrderedAffineCover) (𝒦 : Y.OrderedAffineCover) (lam : 𝒲.ι → 𝒦.ι)
    (hlam : ∀ w, 𝒲.U w ≤ h ⁻¹ᵁ 𝒦.U (lam w))
    (a b n : ℕ) (hn : a + b = n)
    (α : ↥(LinearMap.ker ((OModulePresheaf.unit πY).d 𝒦 a))) (β : ↥(LinearMap.ker ((OModulePresheaf.unit πY).d 𝒦 b))) :
    (OModulePresheaf.unitPullback (πX := πX) h 𝒲 𝒦 lam hlam n ((OModulePresheaf.unit πY).cup 𝒦 a b n hn α.1 β.1) -
        (OModulePresheaf.unit πX).cup 𝒲 a b n hn
          (OModulePresheaf.unitPullback (πX := πX) h 𝒲 𝒦 lam hlam a α.1)
          (OModulePresheaf.unitPullback (πX := πX) h 𝒲 𝒦 lam hlam b β.1))
      ∈ (show Submodule R' ((OModulePresheaf.unit πX).cochain 𝒲 n) from
          match n with
          | 0 => ⊥
          | m + 1 => LinearMap.range ((OModulePresheaf.unit πX).d 𝒲 m)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_unitPullback_cup_sub_cup_unitPullback_mem_of_mem_ker.solution
