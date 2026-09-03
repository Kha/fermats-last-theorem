import Mathlib
import Definitions.Def_ModularCurve_DRResolvedModelPackageLevel
import Definitions.Def_AlgebraicCurve_RelCartier
import P2M.Util
import P2M.Sol.S_ModularCurve_DRResolvedModelPackageLevel_ne_edgePt_and_mem_smoothOffEdges_and_existsUnique_mem_comp_support_of_section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra ModularCurve IsLocalRing

attribute [local instance] ModularCurve.DRModelPackageLevel.neZero_mul

theorem ModularCurve.DRResolvedModelPackageLevel.ne_edgePt_and_mem_smoothOffEdges_and_existsUnique_mem_comp_support_of_section
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] (hpN₀ : ¬ p ∣ N₀) (𝔓 : DRModelPackageLevel N₀ p hpN₀)
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ρO : DRLevel.R p →+* O)
    (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((p : ℕ) : O)})
    (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ] [DecidableEq κ] (toκ : O →+* κ)
    (𝔛reg : DRResolvedModelPackageLevel N₀ p 𝔓 O ρO κ toκ)
    (σ : SchemeHomOver (𝟙 (Spec (CommRingCat.of O))) 𝔛reg.toBase) :
    (∀ (n : 𝔛reg.node) (d : Fin (𝔛reg.width n)), σ.1.base (IsLocalRing.closedPoint O) ≠ 𝔛reg.edgePt n d) ∧
      σ.1.base (IsLocalRing.closedPoint O) ∈ 𝔛reg.smoothOffEdges ∧
      ∃! c : X0MqComponents 𝔛reg.width, σ.1.base (IsLocalRing.closedPoint O) ∈ (𝔛reg.comp c).support := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_DRResolvedModelPackageLevel_ne_edgePt_and_mem_smoothOffEdges_and_existsUnique_mem_comp_support_of_section.solution
