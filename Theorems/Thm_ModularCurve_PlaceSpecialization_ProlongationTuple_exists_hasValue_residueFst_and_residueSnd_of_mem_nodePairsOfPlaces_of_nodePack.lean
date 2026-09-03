import Definitions.Def_ModularCurve_NodeLocalizedPlaces
import P2M.Util
import P2M.Sol.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_hasValue_residueFst_and_residueSnd_of_mem_nodePairsOfPlaces_of_nodePack
attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA
attribute [-simp] ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar

set_option synthInstance.maxHeartbeats 400000

open AlgebraicCurve IsLocalRing ModularCurve
open ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.exists_hasValue_residueFst_and_residueSnd_of_mem_nodePairsOfPlaces_of_nodePack
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ} (R : ProlongationTuple P) [PerfectField k]
    (W : Finset (Place k (modularFunctionFieldC k N)))
    (hmax : ∀ w ∈ W,
      ∀ K : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ K →
        ∃ (K' : IntermediateField ℚ (AlgebraicClosure ℚ)) (_ : FiniteDimensional ℚ K'), K ≤ K' ∧
          ∃ (c : R.NodeCoordinates K' w) (ϖ : ↥(NodeLocalized.coeffSubring A K'))
            (_ : IsLocalRing ↥(R.nodeIntegersOver K' w)) (_ : IsNoetherianRing ↥(R.nodeIntegersOver K' w)),
            (∀ d : ↥(NodeLocalized.coeffSubring A K'), NodeLocalized.redRestrict red K' d = 0 ↔ ∃ d', d = ϖ * d') ∧
            IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K' w) = Ideal.span {R.nodeConst K' w ϖ, c.x, c.y} ∧
            (∀ g : ↥(R.nodeIntegersOver K' w), ∃ o : ↥(NodeLocalized.coeffSubring A K'), ¬ IsUnit (g - R.nodeConst K' w o)) ∧
            ∀ g : ↥(R.nodeIntegersOver K' w),
              (R.nodeResidue₁ w ⟨g, g.2.1⟩ = 0 ∨ 0 ≤ w.ord (R.nodeResidue₁ w ⟨g, g.2.1⟩)) ∧
              (R.nodeResidue₂ w ⟨g, g.2.1⟩ = 0 ∨ 0 ≤ (arithFrobC q k N • w).ord (R.nodeResidue₂ w ⟨g, g.2.1⟩))) :
    ∀ (f : modularFunctionFieldBar (N * q)) (h₁ : f ∈ R.R₁.integers) (h₂ : f ∈ R.R₂.integers),
        ∀ s ∈ nodePairsOfPlaces (arithFrobC q k N) W,
        (∀ V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
          P.reduceFst V = s.1 → 0 ≤ V.ord f) →
        ∃ c : k, s.1.HasValue (R.residue₁ ⟨f, h₁⟩ : modularFunctionFieldC k N) c ∧
                 s.2.HasValue (R.residue₂ ⟨f, h₂⟩ : modularFunctionFieldC k N) c := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_hasValue_residueFst_and_residueSnd_of_mem_nodePairsOfPlaces_of_nodePack.solution
