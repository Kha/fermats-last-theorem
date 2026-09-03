import Mathlib
import Definitions.Def_ModularCurve_DRResolvedModelPackageLevel
import Definitions.Def_AlgebraicCurve_RelCartier
import P2M.Util
import P2M.Sol.S_ModularCurve_DRResolvedModelPackageLevel_isInvertible_comap_comp_subschemeIota

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve

attribute [local instance] ModularCurve.DRModelPackageLevel.neZero_mul

theorem ModularCurve.DRResolvedModelPackageLevel.isInvertible_comap_comp_subschemeIota
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] {hpN₀ : ¬ p ∣ N₀} {𝔓 : DRModelPackageLevel N₀ p hpN₀}
    {O : Type} [CommRing O] {ρO : DRLevel.R p →+* O}
    {κ : Type} [Field κ] [CharP κ p] [IsAlgClosed κ] [DecidableEq κ] {toκ : O →+* κ}
    (R : DRResolvedModelPackageLevel N₀ p 𝔓 O ρO κ toκ)
    (v w : X0MqComponents R.width) (hvw : v ≠ w) :
    ((R.comp v).comap (R.comp w).subschemeι).IsInvertible := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_DRResolvedModelPackageLevel_isInvertible_comap_comp_subschemeIota.solution
