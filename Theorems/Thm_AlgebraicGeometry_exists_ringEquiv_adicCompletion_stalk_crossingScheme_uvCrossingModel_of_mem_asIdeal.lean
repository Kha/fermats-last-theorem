import Mathlib
import Definitions.Def_MvPolynomial_CrossingResolutionScheme
import Definitions.Def_ModularCurve_UVCrossingModel
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_ringEquiv_adicCompletion_stalk_crossingScheme_uvCrossingModel_of_mem_asIdeal
attribute [-instance] instTopologicallyFGOfFiniteType

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry IsLocalRing MvPolynomial ModularCurve

theorem AlgebraicGeometry.exists_ringEquiv_adicCompletion_stalk_crossingScheme_uvCrossingModel_of_mem_asIdeal
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (ϖ : O) (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {ϖ})
    (E : ℕ) (hE : 1 ≤ E) (w : Oˣ) (a : O) (ha : a = (w : O) * ϖ ^ E)
    (m : ↥(CrossingQuotient.crossingScheme a))
    [IsNoetherianRing ((CrossingQuotient.crossingScheme a).presheaf.stalk m)]
    (hm : CrossingQuotient.U a ∈ m.asIdeal ∧ CrossingQuotient.V a ∈ m.asIdeal) :
    letI φ : CrossingQuotient O a →+* Γ(CrossingQuotient.crossingScheme a, ⊤) :=
      (Scheme.ΓSpecIso (CommRingCat.of (CrossingQuotient O a))).inv.hom
    letI germ : Γ(CrossingQuotient.crossingScheme a, ⊤) → (CrossingQuotient.crossingScheme a).presheaf.stalk m :=
      fun t => ((CrossingQuotient.crossingScheme a).presheaf.germ ⊤ m trivial).hom t
    letI B := (CrossingQuotient.crossingScheme a).presheaf.stalk m
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
        UVCrossingModel.V ((σ ϖ) ^ E) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_ringEquiv_adicCompletion_stalk_crossingScheme_uvCrossingModel_of_mem_asIdeal.solution
