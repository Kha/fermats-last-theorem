import Definitions.Def_ModularCurve_NodeLocalizedPlaces
import Definitions.Def_ModularCurve_UVCrossingModel
import Definitions.Def_ModularCurve_UVCrossingGaussOrder
import P2M.Util
import P2M.Sol.S_ModularCurve_PlaceSpecialization_ProlongationTuple_gaussOrder_snd_end_ringEquiv_adicCompletion_eq_add_of_eq_nodeConst_pow_mul
set_option autoImplicit false
open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.UVCrossingModel
open ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.gaussOrder_snd_end_ringEquiv_adicCompletion_eq_add_of_eq_nodeConst_pow_mul
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (R : ProlongationTuple P) [IsAlgClosed k] [DecidableEq k] (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (w : Place k (modularFunctionFieldC k N))
    [IsLocalRing ↥(R.nodeIntegersOver K w)]
    (ϖ : ↥(NodeLocalized.coeffSubring A K)) (E : ℕ) (hE : 1 ≤ E)
    {W : Type*} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W]
    (π : W) (hπ : Irreducible π)
    (ι : AdicCompletion (maximalIdeal ↥(R.nodeIntegersOver K w)) ↥(R.nodeIntegersOver K w)
          ≃+* UVCrossingModel W (π ^ E))
    (hιϖ : ι (algebraMap _ _ (R.nodeConst K w ϖ)) = const (π ^ E) π)
    (hord : ∀ (f : ↥(R.nodeIntegersOver K w)) (n : ℕ), R.nodeResidue₂ w ⟨f, f.2.1⟩ ≠ 0 →
        (arithFrobC q k N • w).ord (R.nodeResidue₂ w ⟨f, f.2.1⟩) = (n : ℤ) →
        ∃ γ, IsUnit γ ∧ ι (algebraMap _ _ f) - γ * U (π ^ E) ^ n ∈ Ideal.span {const (π ^ E) π, V (π ^ E)})
    (x x' u : ↥(R.nodeIntegersOver K w)) (n : ℕ) (hu : R.nodeResidue₂ w ⟨u, u.2.1⟩ ≠ 0)
    (hn : (arithFrobC q k N • w).ord (R.nodeResidue₂ w ⟨u, u.2.1⟩) = (n : ℤ))
    (d : ℕ) (hrel : x = R.nodeConst K w ϖ ^ d * u * x') :
    gaussOrder (IsDiscreteValuationRing.addVal W) (π ^ E) E 0 (ι (algebraMap _ _ x)) =
      d + gaussOrder (IsDiscreteValuationRing.addVal W) (π ^ E) E 0 (ι (algebraMap _ _ x')) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_gaussOrder_snd_end_ringEquiv_adicCompletion_eq_add_of_eq_nodeConst_pow_mul.solution
