import Mathlib
import Definitions.Def_ModularCurve_DRResolvedModelPackageLevel
import Definitions.Def_AlgebraicCurve_RelCartier
import P2M.Util
import P2M.Sol.S_ModularCurve_DRResolvedModelPackageLevel_eta_notMem_range_of_comp_toBase_eq_id

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve

attribute [local instance] ModularCurve.DRModelPackageLevel.neZero_mul

theorem ModularCurve.DRResolvedModelPackageLevel.eta_notMem_range_of_comp_toBase_eq_id
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] {hpN₀ : ¬ p ∣ N₀} {𝔓 : DRModelPackageLevel N₀ p hpN₀}
    {O : Type} [CommRing O] [IsLocalRing O] {ρO : DRLevel.R p →+* O}
    (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((p : ℕ) : O)})
    {κ : Type} [Field κ] [CharP κ p] [IsAlgClosed κ] [DecidableEq κ] {toκ : O →+* κ}
    (R : DRResolvedModelPackageLevel N₀ p 𝔓 O ρO κ toκ)
    (σ : Spec (CommRingCat.of O) ⟶ R.Y) (hσ : σ ≫ R.toBase = 𝟙 _) (c : X0MqComponents R.width) :
    R.η c ∉ Set.range σ.base := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_DRResolvedModelPackageLevel_eta_notMem_range_of_comp_toBase_eq_id.solution
