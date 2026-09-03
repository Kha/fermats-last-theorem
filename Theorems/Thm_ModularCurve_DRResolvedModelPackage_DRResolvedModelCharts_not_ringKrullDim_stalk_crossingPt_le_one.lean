import Mathlib
import Definitions.Def_ModularCurve_DRResolvedModelPackageV4
import Definitions.Def_ModularCurve_DRResolvedModelCharts
import Definitions.Def_MvPolynomial_CrossingResolutionScheme
import P2M.Util
import P2M.Sol.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_not_ringKrullDim_stalk_crossingPt_le_one

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial MvPolynomial.CrossingQuotient ModularCurve

theorem ModularCurve.DRResolvedModelPackage.DRResolvedModelCharts.not_ringKrullDim_stalk_crossingPt_le_one
    {p : ℕ} [Fact p.Prime] {𝔛 : DRModelPackage p}
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (ϖ : O) (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {ϖ})
    {κ : Type} [Field κ] [CharP κ p] [IsAlgClosed κ] {toκ : O →+* κ}
    {𝔛reg : DRResolvedModelPackage p 𝔛 O κ toκ}
    {Fc : ∀ e : ℕ, Fin (e + 1) → (Resolution ϖ e).IdealSheafData}
    (ch : 𝔛reg.DRResolvedModelCharts ϖ Fc) (n : 𝔛reg.node) :
    ¬ ringKrullDim ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk (𝔛reg.crossingPt n)) ≤ 1 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_not_ringKrullDim_stalk_crossingPt_le_one.solution
