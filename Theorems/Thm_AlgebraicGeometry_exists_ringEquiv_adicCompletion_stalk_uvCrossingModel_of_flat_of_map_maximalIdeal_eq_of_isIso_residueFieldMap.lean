import Mathlib
import Definitions.Def_MvPolynomial_CrossingResolutionScheme
import Definitions.Def_ModularCurve_UVCrossingModel
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_ringEquiv_adicCompletion_stalk_uvCrossingModel_of_flat_of_map_maximalIdeal_eq_of_isIso_residueFieldMap
attribute [-instance] instTopologicallyFGOfFiniteType

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry open IsLocalRing hiding exists_ringEquiv_adicCompletion_uvCrossingModel_of_mul_eq_pow_mul_unit exists_adicCompletion_ringEquiv_of_flat_of_map_maximalIdeal_eq_of_residue_surjective open MvPolynomial ModularCurve

theorem AlgebraicGeometry.exists_ringEquiv_adicCompletion_stalk_uvCrossingModel_of_flat_of_map_maximalIdeal_eq_of_isIso_residueFieldMap
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (ϖ : O) (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {ϖ})
    (E : ℕ) (hE : 1 ≤ E) (w : Oˣ) (a : O) (ha : a = (w : O) * ϖ ^ E)
    (Y : Scheme.{0}) (g : Y ⟶ CrossingQuotient.crossingScheme a) (y : ↥Y)
    [IsNoetherianRing (Y.presheaf.stalk y)]
    (hy : CrossingQuotient.U a ∈ (g.base y).asIdeal ∧ CrossingQuotient.V a ∈ (g.base y).asIdeal)
    (hpt : (g.stalkMap y).hom.Flat ∧
      Ideal.map (g.stalkMap y).hom (IsLocalRing.maximalIdeal _) = IsLocalRing.maximalIdeal _ ∧
      IsIso (g.residueFieldMap y)) :
    letI φ : CrossingQuotient O a →+* Γ(CrossingQuotient.crossingScheme a, ⊤) :=
      (Scheme.ΓSpecIso (CommRingCat.of (CrossingQuotient O a))).inv.hom
    letI germ : Γ(CrossingQuotient.crossingScheme a, ⊤) → Y.presheaf.stalk y :=
      fun t => (Y.presheaf.germ ⊤ y trivial).hom ((g.appTop).hom t)
    letI B := Y.presheaf.stalk y
    ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W)
      (_ : IsAdicComplete (IsLocalRing.maximalIdeal W) W) (σ : O →+* W)
      (_ : IsLocalRing.maximalIdeal W = Ideal.span {σ ϖ})
      (_ : Function.Surjective ((IsLocalRing.residue W).comp σ))
      (ι : AdicCompletion (IsLocalRing.maximalIdeal B) B ≃+* UVCrossingModel W ((σ ϖ) ^ E)),
      (∀ o : O, ι (algebraMap B (AdicCompletion (IsLocalRing.maximalIdeal B) B) (germ (φ (algebraMap O _ o)))) =
        UVCrossingModel.const ((σ ϖ) ^ E) (σ o)) ∧
      (∃ w' : (UVCrossingModel W ((σ ϖ) ^ E))ˣ,
        ι (algebraMap B (AdicCompletion (IsLocalRing.maximalIdeal B) B) (germ (φ (CrossingQuotient.U a)))) =
          UVCrossingModel.U ((σ ϖ) ^ E) * w') ∧
      ι (algebraMap B (AdicCompletion (IsLocalRing.maximalIdeal B) B) (germ (φ (CrossingQuotient.V a)))) =
        UVCrossingModel.V ((σ ϖ) ^ E) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_ringEquiv_adicCompletion_stalk_uvCrossingModel_of_flat_of_map_maximalIdeal_eq_of_isIso_residueFieldMap.solution
