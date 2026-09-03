import Mathlib
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Place_existsUnique_forall_mem_iff_adjoin_sup_of_isAlgebraic_of_forall_exists_sub_mem
attribute [-instance] AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion
attribute [-simp] AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom

set_option autoImplicit false

open AlgebraicCurve IsLocalRing

theorem AlgebraicCurve.Place.existsUnique_forall_mem_iff_adjoin_sup_of_isAlgebraic_of_forall_exists_sub_mem
    {k₀ L F : Type} [Field k₀] [Field L] [CharZero L] [Field F] [Algebra k₀ L] [Algebra k₀ F] [Algebra L F]
    [IsScalarTower k₀ L F]
    (F₀ : IntermediateField k₀ F) (K₁ : IntermediateField k₀ L)
    (hgen : IntermediateField.adjoin k₀ (Set.range (algebraMap L F)) ⊔ F₀ = ⊤)
    (halg : ∀ x : L, IsAlgebraic ↥K₁ x)
    (V₁ : ValuationSubring ↥(IntermediateField.adjoin k₀ (⇑(algebraMap L F) '' (↑K₁ : Set L)) ⊔ F₀))
    (hK₁V : ∀ (x : ↥K₁) (hx : algebraMap L F (x : L) ∈ IntermediateField.adjoin k₀ (⇑(algebraMap L F) '' (↑K₁ : Set L)) ⊔ F₀),
      (⟨algebraMap L F (x : L), hx⟩ : ↥(IntermediateField.adjoin k₀ (⇑(algebraMap L F) '' (↑K₁ : Set L)) ⊔ F₀)) ∈ V₁)
    [IsDiscreteValuationRing ↥V₁]
    (hrat : ∀ v : ↥V₁, ∃ (x : ↥K₁) (hx : algebraMap L F (x : L) ∈ IntermediateField.adjoin k₀ (⇑(algebraMap L F) '' (↑K₁ : Set L)) ⊔ F₀),
      v - ⟨⟨algebraMap L F (x : L), hx⟩, hK₁V x hx⟩ ∈ maximalIdeal ↥V₁) :
    (∃! P : Place L F, ∀ f : ↥(IntermediateField.adjoin k₀ (⇑(algebraMap L F) '' (↑K₁ : Set L)) ⊔ F₀), (f : F) ∈ P.toValuationSubring ↔ f ∈ V₁) ∧
    (∀ P : Place L F, (∀ f : ↥(IntermediateField.adjoin k₀ (⇑(algebraMap L F) '' (↑K₁ : Set L)) ⊔ F₀), (f : F) ∈ P.toValuationSubring ↔ f ∈ V₁) → P.IsRational) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Place_existsUnique_forall_mem_iff_adjoin_sup_of_isAlgebraic_of_forall_exists_sub_mem.solution
