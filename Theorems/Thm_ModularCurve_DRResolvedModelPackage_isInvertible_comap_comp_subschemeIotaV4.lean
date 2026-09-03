import Mathlib
import Definitions.Def_ModularCurve_DRResolvedModelPackageV4
import Definitions.Def_AlgebraicCurve_RelCartier
import P2M.Util
import P2M.Sol.S_ModularCurve_DRResolvedModelPackage_isInvertible_comap_comp_subschemeIotaV4

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve

theorem ModularCurve.DRResolvedModelPackage.isInvertible_comap_comp_subschemeIotaV4
    (p : ℕ) [Fact p.Prime] {𝔛 : DRModelPackage p} {O : Type} [CommRing O]
    {κ : Type} [Field κ] [CharP κ p] [IsAlgClosed κ] {toκ : O →+* κ} (R : DRResolvedModelPackage p 𝔛 O κ toκ)
    (v w : X0MqComponents R.width) (hvw : v ≠ w) :
    ((R.comp v).comap (R.comp w).subschemeι).IsInvertible := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_DRResolvedModelPackage_isInvertible_comap_comp_subschemeIotaV4.solution
