import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCechCup
import Definitions.Def_AlgebraicGeometry_DoubleComplex
import Definitions.Def_AlgebraicGeometry_BiCech
import Definitions.Def_AlgebraicGeometry_BoundedCochainTensor
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCochainPullback
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_d_comp_d
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_unitPullback_prodCover_cup_sub_cup_unitPullback_mem
attribute [-instance] AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableOSub

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits TensorProduct AlgebraicGeometry

universe u

theorem AlgebraicGeometry.OModulePresheaf.unitPullback_prodCover_cup_sub_cup_unitPullback_mem
    {k : Type u} [Field k] {X Y : Scheme.{u}}
    (πX : X ⟶ Spec (CommRingCat.of k)) (πY : Y ⟶ Spec (CommRingCat.of k)) [IsSeparated πX] [IsSeparated πY]
    (𝔘 : X.OrderedAffineCover) (𝔙 : Y.OrderedAffineCover)
    (haff : ∀ i j, IsAffineOpen ((𝔘.preimageFamily (pullback.fst πX πY)).U i ⊓ (𝔙.preimageFamily (pullback.snd πX πY)).U j))
    (hcov : ⨆ ij : 𝔘.ι × 𝔙.ι,
      (𝔘.preimageFamily (pullback.fst πX πY)).U ij.1 ⊓ (𝔙.preimageFamily (pullback.snd πX πY)).U ij.2 = ⊤)

    (𝒲 : (pullback πX πY).OrderedAffineCover) (lam₁ : 𝒲.ι → 𝔘.ι) (lam₂ : 𝒲.ι → 𝔙.ι)
    (h₁ : ∀ w, 𝒲.U w ≤ pullback.fst πX πY ⁻¹ᵁ 𝔘.U (lam₁ w))
    (h₂ : ∀ w, 𝒲.U w ≤ pullback.snd πX πY ⁻¹ᵁ 𝔙.U (lam₂ w))
    (hμ : ∀ w, 𝒲.U w ≤ (𝟙 (pullback πX πY)) ⁻¹ᵁ
      ((𝔘.preimageFamily (pullback.fst πX πY)).prodCover (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov).U
        (toLex (lam₁ w, lam₂ w)))
    (p q n : ℕ) (hn : p + q = n)
    (α : ↥(LinearMap.ker ((OModulePresheaf.unit πX).d 𝔘 p))) (β : ↥(LinearMap.ker ((OModulePresheaf.unit πY).d 𝔙 q))) :
    (OModulePresheaf.unitPullback (πX := pullback.fst πX πY ≫ πX) (𝟙 (pullback πX πY)) 𝒲
        ((𝔘.preimageFamily (pullback.fst πX πY)).prodCover (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov)
        (fun w => toLex (lam₁ w, lam₂ w)) hμ n
        ((OModulePresheaf.unit (pullback.fst πX πY ≫ πX)).cup
          ((𝔘.preimageFamily (pullback.fst πX πY)).prodCover (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov) p q n hn
          (OModulePresheaf.unitPullback (πX := pullback.fst πX πY ≫ πX) (pullback.fst πX πY)
            ((𝔘.preimageFamily (pullback.fst πX πY)).prodCover (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov) 𝔘
            (fun ij => (ofLex ij).1) (fun ij => inf_le_left) p α.1)
          (OModulePresheaf.unitPullback (πX := pullback.fst πX πY ≫ πX) (pullback.snd πX πY)
            ((𝔘.preimageFamily (pullback.fst πX πY)).prodCover (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov) 𝔙
            (fun ij => (ofLex ij).2) (fun ij => inf_le_right) q β.1)) -
      (OModulePresheaf.unit (pullback.fst πX πY ≫ πX)).cup 𝒲 p q n hn
        (OModulePresheaf.unitPullback (πX := pullback.fst πX πY ≫ πX) (pullback.fst πX πY) 𝒲 𝔘 lam₁ h₁ p α.1)
        (OModulePresheaf.unitPullback (πX := pullback.fst πX πY ≫ πX) (pullback.snd πX πY) 𝒲 𝔙 lam₂ h₂ q β.1))
      ∈ (show Submodule k ((OModulePresheaf.unit (pullback.fst πX πY ≫ πX)).cochain 𝒲 n) from
          match n with
          | 0 => ⊥
          | m + 1 => LinearMap.range ((OModulePresheaf.unit (pullback.fst πX πY ≫ πX)).d 𝒲 m)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_unitPullback_prodCover_cup_sub_cup_unitPullback_mem.solution
