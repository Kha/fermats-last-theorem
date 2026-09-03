import Mathlib
import Definitions.Def_ModularCurve_DRResolvedModelPackageLevel
import P2M.Util
import P2M.Sol.S_ModularCurve_DRResolvedModelPackageLevel_mem_support_comp_inl_zero_of_not_mem_range

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve

attribute [local instance] ModularCurve.DRModelPackageLevel.neZero_mul

theorem ModularCurve.DRResolvedModelPackageLevel.mem_support_comp_inl_zero_of_not_mem_range
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] (hpN₀ : ¬ p ∣ N₀) (𝔓 : DRModelPackageLevel N₀ p hpN₀)
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ρO : DRLevel.R p →+* O)
    (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((p : ℕ) : O)})
    (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ] [DecidableEq κ] (toκ : O →+* κ)
    (𝔛reg : DRResolvedModelPackageLevel N₀ p 𝔓 O ρO κ toκ)
    (t : Spec (CommRingCat.of O) ⟶ 𝔛reg.Y) (ht : t ≫ 𝔛reg.toBase = 𝟙 _)
    (hout : (t ≫ 𝔛reg.toDR).base (IsLocalRing.closedPoint O) ∉ Set.range (𝔓.comp κ (toκ.comp ρO) 1 ≫ DRLevel.bcMap ρO toκ).base) :
    t.base (IsLocalRing.closedPoint O) ∈ ((𝔛reg.comp (Sum.inl 0)).support : Set ↥𝔛reg.Y) ∧
      ∀ w, w ≠ Sum.inl 0 → t.base (IsLocalRing.closedPoint O) ∉ ((𝔛reg.comp w).support : Set ↥𝔛reg.Y) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_DRResolvedModelPackageLevel_mem_support_comp_inl_zero_of_not_mem_range.solution
