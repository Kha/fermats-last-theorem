import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCochainPullback
import Definitions.Def_AlgebraicGeometry_DoubleComplex
import Definitions.Def_AlgebraicGeometry_OModulePresheafLerayDoubleComplex
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_Leray_exists_dTot_eq_single_biAug_unitPullback_sub_single_id

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.OModulePresheaf.Leray.exists_dTot_eq_single_biAug_unitPullback_sub_single_id
    {R : Type u} [CommRing R] {X : Scheme.{u}} (π : X ⟶ Spec (CommRingCat.of R))
    (𝔓 𝒲 : X.OrderedAffineCover) (lam : 𝒲.ι → 𝔓.ι) (hlam : ∀ w, 𝒲.U w ≤ (𝟙 X) ⁻¹ᵁ 𝔓.U (lam w)) :
    (∀ z : ↥(LinearMap.ker ((OModulePresheaf.unit (𝟙 X ≫ π)).d 𝔓 0)),
        OModulePresheaf.Leray.biAug (𝟙 X) π 𝔓 𝒲 0 (OModulePresheaf.unitPullback (πX := 𝟙 X ≫ π) (𝟙 X) 𝒲 𝔓 lam hlam 0 z.1) =
          (fun στ : OModulePresheaf.Leray.BiIdx 𝔓 𝒲 0 0 => (X.presheaf.map (homOfLE ((inf_le_right :
            OModulePresheaf.Leray.biOpen (𝟙 X) 𝔓 𝒲 0 0 στ.1 στ.2 ≤ (𝟙 X) ⁻¹ᵁ 𝔓.inter στ.1).trans
              (Scheme.Hom.id_preimage (𝔓.inter στ.1)).le)).op).hom (z.1 στ.1) :
            OModulePresheaf.Leray.biC (𝟙 X) π 𝔓 𝒲 0 0)) ∧
    ∀ (n : ℕ) (z : ↥(LinearMap.ker ((OModulePresheaf.unit (𝟙 X ≫ π)).d 𝔓 (n + 1)))),
      ∃ h : DoubleComplex.Tot (OModulePresheaf.Leray.LerayDblCpx (𝟙 X) π 𝔓 𝒲) n,
        DoubleComplex.dTot (OModulePresheaf.Leray.LerayDblCpx (𝟙 X) π 𝔓 𝒲) n h =
          Pi.single (M := fun i : DoubleComplex.Diag (n + 1) => (OModulePresheaf.Leray.LerayDblCpx (𝟙 X) π 𝔓 𝒲).C i.1.1 i.1.2)
              ⟨(0, n + 1), by omega⟩
              (OModulePresheaf.Leray.biAug (𝟙 X) π 𝔓 𝒲 (n + 1)
                (OModulePresheaf.unitPullback (πX := 𝟙 X ≫ π) (𝟙 X) 𝒲 𝔓 lam hlam (n + 1) z.1)) -
            Pi.single (M := fun i : DoubleComplex.Diag (n + 1) => (OModulePresheaf.Leray.LerayDblCpx (𝟙 X) π 𝔓 𝒲).C i.1.1 i.1.2)
              ⟨(n + 1, 0), by omega⟩
              (fun στ : OModulePresheaf.Leray.BiIdx 𝔓 𝒲 (n + 1) 0 => (X.presheaf.map (homOfLE ((inf_le_right :
                OModulePresheaf.Leray.biOpen (𝟙 X) 𝔓 𝒲 (n + 1) 0 στ.1 στ.2 ≤ (𝟙 X) ⁻¹ᵁ 𝔓.inter στ.1).trans
                  (Scheme.Hom.id_preimage (𝔓.inter στ.1)).le)).op).hom (z.1 στ.1)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_Leray_exists_dTot_eq_single_biAug_unitPullback_sub_single_id.solution
