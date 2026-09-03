import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_DoubleComplex
import Definitions.Def_AlgebraicGeometry_BiCech
import Definitions.Def_AlgebraicGeometry_BoundedCochainTensor
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCochainPullback
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_biCech_preimageFamily_equiv_tensor_cochain_pinned
attribute [-simp] AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits TensorProduct AlgebraicGeometry

universe u

theorem AlgebraicGeometry.OModulePresheaf.exists_biCech_preimageFamily_equiv_tensor_cochain_pinned
    {k : Type u} [Field k] {X Y : Scheme.{u}}
    (πX : X ⟶ Spec (CommRingCat.of k)) (πY : Y ⟶ Spec (CommRingCat.of k)) [IsSeparated πX] [IsSeparated πY]
    (𝔘 : X.OrderedAffineCover) (𝔙 : Y.OrderedAffineCover) :
    ∃ e : ∀ p q : ℕ,
        OModulePresheaf.BiCech.C (OModulePresheaf.unit (pullback.fst πX πY ≫ πX))
            (𝔘.preimageFamily (pullback.fst πX πY)) (𝔙.preimageFamily (pullback.snd πX πY)) p q ≃ₗ[k]
          ((OModulePresheaf.unit πX).cochain 𝔘 p ⊗[k] (OModulePresheaf.unit πY).cochain 𝔙 q),

      (∀ (p q : ℕ) (c : OModulePresheaf.BiCech.C (OModulePresheaf.unit (pullback.fst πX πY ≫ πX))
            (𝔘.preimageFamily (pullback.fst πX πY)) (𝔙.preimageFamily (pullback.snd πX πY)) p q),
        e (p + 1) q (OModulePresheaf.BiCech.dH (OModulePresheaf.unit (pullback.fst πX πY ≫ πX)) _ _ p q c) =
          ((OModulePresheaf.unit πX).d 𝔘 p).rTensor _ (e p q c)) ∧
      (∀ (p q : ℕ) (c : OModulePresheaf.BiCech.C (OModulePresheaf.unit (pullback.fst πX πY ≫ πX))
            (𝔘.preimageFamily (pullback.fst πX πY)) (𝔙.preimageFamily (pullback.snd πX πY)) p q),
        e p (q + 1) (OModulePresheaf.BiCech.dV (OModulePresheaf.unit (pullback.fst πX πY ≫ πX)) _ _ p q c) =
          ((OModulePresheaf.unit πY).d 𝔙 q).lTensor _ (e p q c)) ∧

      (∀ (p q : ℕ) (α : (OModulePresheaf.unit πX).cochain 𝔘 p) (β : (OModulePresheaf.unit πY).cochain 𝔙 q)
          (s : 𝔘.Idx p) (t : 𝔙.Idx q),
        (e p q).symm (α ⊗ₜ[k] β) (s, t) =
          ((pullback πX πY).presheaf.map (homOfLE (inf_le_left.trans
              (le_of_eq (Scheme.OrderedAffineCover.preimage_iInf_fin (pullback.fst πX πY) (fun j => 𝔘.U (s.1 j))).symm))).op).hom
            (((pullback.fst πX πY).app (𝔘.inter s)).hom (α s)) *
          ((pullback πX πY).presheaf.map (homOfLE (inf_le_right.trans
              (le_of_eq (Scheme.OrderedAffineCover.preimage_iInf_fin (pullback.snd πX πY) (fun j => 𝔙.U (t.1 j))).symm))).op).hom
            (((pullback.snd πX πY).app (𝔙.inter t)).hom (β t))) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_biCech_preimageFamily_equiv_tensor_cochain_pinned.solution
