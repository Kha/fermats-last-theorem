import Mathlib
import Definitions.Def_ModularCurve_NodeDepth
import Definitions.Def_ModularCurve_UVCrossingModel
import P2M.Util
import P2M.Sol.S_ModularCurve_PlaceSpecialization_ProlongationTuple_hasValue_nodeResidueSnd_div_nodeResidueSnd_x_pow_of_sub_mul_U_pow_mem_of_hasValue

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option autoImplicit false

universe u

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization
theorem ModularCurve.PlaceSpecialization.ProlongationTuple.hasValue_nodeResidueSnd_div_nodeResidueSnd_x_pow_of_sub_mul_U_pow_mem_of_hasValue
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (R : ProlongationTuple P) [PerfectField k]
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (w : Place k (modularFunctionFieldC k N)) (c : R.NodeCoordinates K w)
    (ϖ : ↥(NodeLocalized.coeffSubring A K))
    [IsLocalRing ↥(R.nodeIntegersOver K w)] [IsNoetherianRing ↥(R.nodeIntegersOver K w)]
    (hmax : IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w) = Ideal.span {R.nodeConst K w ϖ, c.x, c.y})
    (hres : ∀ g : ↥(R.nodeIntegersOver K w), ∃ o : ↥(NodeLocalized.coeffSubring A K), ¬ IsUnit (g - R.nodeConst K w o))
    (hϖ : ∀ d : ↥(NodeLocalized.coeffSubring A K), NodeLocalized.redRestrict red K d = 0 ↔ ∃ d', d = ϖ * d')
    (hVI : R.ValueIntegralityLaw w) [DecidableEq k] (hwss : w ∈ ssPlaces q N k)
    {W : Type u} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (IsLocalRing.maximalIdeal W) W]
    (π : W) (hπ : Irreducible π) (E : ℕ) (hE : 1 ≤ E)
    (ι : AdicCompletion (IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w)) ↥(R.nodeIntegersOver K w)
          ≃+* UVCrossingModel W (π ^ E))

    (wmap : ↥(NodeLocalized.coeffSubring A K) →+* W) (hwϖ : wmap ϖ = π)
    (hιw : ∀ o : ↥(NodeLocalized.coeffSubring A K), ι (algebraMap _ _ (R.nodeConst K w o)) = UVCrossingModel.const (π ^ E) (wmap o))
    (ρ : W →+* k) (hρ : ∀ o : ↥(NodeLocalized.coeffSubring A K), ρ (wmap o) = NodeLocalized.redRestrict red K o)

    (V₀ : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) (hV₀ : P.reduceFst V₀ = w)
    (hVAL : ∀ (g : ↥(R.nodeIntegersOver K w)) (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
      (hV : P.reduceFst V = w),
      (arithFrobC q k N • w).HasValue (R.nodeResidue₂ w ⟨(g : ↥(modularFunctionFieldBar (N * q))), g.2.1⟩ : ↥(modularFunctionFieldC k N))
        (red ⟨V.evalAt (g : ↥(modularFunctionFieldBar (N * q))),
          hVI (g : ↥(modularFunctionFieldBar (N * q))) (R.nodeIntegersOver_le K w g.2) V hV⟩))
    (αU : UVCrossingModel W (π ^ E)) (hαU : IsUnit αU) (hιx : ι (algebraMap _ _ c.x) = UVCrossingModel.U (π ^ E) * αU)
    (βV : UVCrossingModel W (π ^ E)) (hβV : IsUnit βV) (hιy : ι (algebraMap _ _ c.y) = UVCrossingModel.V (π ^ E) * βV)
    (Gα : MvPowerSeries (Fin 2) W) (hGα : UVCrossingModel.mk (π ^ E) Gα = αU)
    (f : ↥(R.nodeIntegersOver K w)) (m : ℕ)
    (hf : R.nodeResidue₂ w ⟨(f : ↥(modularFunctionFieldBar (N * q))), f.2.1⟩ ≠ 0)
    (hm : (arithFrobC q k N • w).ord (R.nodeResidue₂ w ⟨(f : ↥(modularFunctionFieldBar (N * q))), f.2.1⟩) = (m : ℤ))
    (γ : UVCrossingModel W (π ^ E)) (hγ : IsUnit γ)
    (hfγ : ι (algebraMap _ _ f) - γ * UVCrossingModel.U (π ^ E) ^ m ∈ Ideal.span {UVCrossingModel.const (π ^ E) π, UVCrossingModel.V (π ^ E)})
    (Gγ : MvPowerSeries (Fin 2) W) (hGγ : UVCrossingModel.mk (π ^ E) Gγ = γ) :
    (arithFrobC q k N • w).HasValue
      ((R.nodeResidue₂ w ⟨(f : ↥(modularFunctionFieldBar (N * q))), f.2.1⟩ : ↥(modularFunctionFieldC k N)) /
        (R.nodeResidue₂ w ⟨(c.x : ↥(modularFunctionFieldBar (N * q))), c.x.2.1⟩ : ↥(modularFunctionFieldC k N)) ^ m)
      (ρ (MvPowerSeries.constantCoeff Gγ) * (ρ (MvPowerSeries.constantCoeff Gα))⁻¹ ^ m) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_hasValue_nodeResidueSnd_div_nodeResidueSnd_x_pow_of_sub_mul_U_pow_mem_of_hasValue.solution
