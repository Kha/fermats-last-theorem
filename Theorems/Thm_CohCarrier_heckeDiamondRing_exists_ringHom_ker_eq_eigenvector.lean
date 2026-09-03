import Definitions.Def_CohCarrier_HeckeDiamondRing
import Mathlib.FieldTheory.IsAlgClosed.Basic
import P2M.Util
import P2M.Sol.S_CohCarrier_heckeDiamondRing_exists_ringHom_ker_eq_eigenvector
attribute [-instance] CuspForm.TWLevel.HeckeRing.instAlgebra CuspForm.TWLevel.heckeSubalgebra_isMulCommutative CuspForm.TWLevel.HeckeRing.instInhabited CuspForm.TWLevel.HeckeRing.instCommRing CuspForm.TWLevel.level_neZero CuspForm.TWLevel.instModuleFreeAlgCarrier CuspForm.AuxLevel.instModuleFreeAlgCarrier CuspForm.heckeAlgebra.instCommRing CuspForm.heckeAlgebra.instIsMulCommutative CuspForm.heckeAlgebra.instIsAddTorsionFree WeierstrassCurve.Affine.Point.instFinite CohCarrier.GammaHLower_finiteIndex
attribute [-simp] CuspForm.TWLevel.opML_apply CuspForm.TWLevel.HeckeRing.act_diamond CuspForm.TWLevel.HeckeRing.act_T CuspForm.TWLevel.diamondLin_apply CuspForm.TWLevel.Gen.U.sizeOf_spec CuspForm.TWLevel.Gen.U.injEq CuspForm.TWLevel.Gen.T.sizeOf_spec CuspForm.TWLevel.Gen.T.injEq CuspForm.TWLevel.piQ_apply CuspForm.AuxLevel.Gen.mk.injEq CuspForm.AuxLevel.Gen.mk.sizeOf_spec CuspForm.heckeAlgebra.coe_U CuspForm.heckeAlgebra.coe_T ModularForm.coe_heckeTLin_apply CuspForm.coe_heckeULin_apply CuspForm.coe_heckeTLin_apply ModularForm.coe_heckeULin_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL CohCarrier.uMat_apply_10 CohCarrier.rightQuotEquivOfDvd_apply CohCarrier.uMat_apply_11 CohCarrier.uMat_apply_01 CohCarrier.uMat_apply_00 CohCarrier.coe_uElt

set_option autoImplicit false

theorem CohCarrier.heckeDiamondRing.exists_ringHom_ker_eq_eigenvector
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [CharZero 𝒪]
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (S : Set ℕ) (H' : Subgroup (ZMod M)ˣ)
    (hcomm : ∀ a ∈ CohCarrier.heckeDiamondGens M H S H' 𝒪, ∀ b ∈ CohCarrier.heckeDiamondGens M H S H' 𝒪,
      a * b = b * a)
    (𝔭 : Ideal ↥(CohCarrier.heckeDiamondRing M H S H' 𝒪)) [𝔭.IsPrime]
    (h𝔭 : ∀ n : ℤ, (n : ↥(CohCarrier.heckeDiamondRing M H S H' 𝒪)) ∈ 𝔭 → n = 0)
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [CharZero Ω] :
    ∃ (χ : ↥(CohCarrier.heckeDiamondRing M H S H' 𝒪) →+* Ω) (e : (ZMod M)ˣ →* Ωˣ)
      (φ : CohCarrier.H1 M H Ω),
      RingHom.ker χ = 𝔭 ∧ φ ≠ 0 ∧
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S) (hℓM : ¬ ℓ ∣ M),
        (haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩; CohCarrier.heckeT M H ℓ Ω φ) =
          χ (CohCarrier.heckeDiamondRing.T M H S H' 𝒪 ℓ hℓ hℓS hℓM) • φ) ∧
      (∀ u : (ZMod M)ˣ, CohCarrier.diamondL M H Ω u φ = (e u : Ω) • φ) ∧
      (∀ (u : (ZMod M)ˣ) (hu : u ∈ H'),
        (e u : Ω) = χ (CohCarrier.heckeDiamondRing.diamond M H S H' 𝒪 u hu)) := by p2m_exact_reverting @_root_.P2MW.S_CohCarrier_heckeDiamondRing_exists_ringHom_ker_eq_eigenvector.solution
