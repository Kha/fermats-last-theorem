import Mathlib
import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_GlueData
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_GluedPic0
import Definitions.Def_AlgebraicCurve_PlaceEvaluationAlgebra
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import P2M.Util
import P2M.Sol.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_commonUnit_ord_eq_one_orderTables_of_realisation
set_option Elab.async false
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.exists_commonUnit_ord_eq_one_orderTables_of_realisation
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    [CharP (ResidueField A) q] [IsAlgClosed (ResidueField A)] [DecidableEq (ResidueField A)]
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr (ResidueField A) (IsLocalRing.residue A) hα hβ}
    [HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))]
    [IsCurveOver (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))]
    [IsCurveOver (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) N)]
    (R : ProlongationTuple P) (hR : R.IsModel) (hO : R.OrderLawFixed)
    (W : Finset (Place (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) N))) (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N (ResidueField A))
    (hRL : R.RegularityLaw W) (hNV : R.NodeValueLaw W) (hqN : ¬ q ∣ N)

    (hcusp : ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), ¬ IsAffineGeomPlace (ResidueField A) N (P.reduceFst V) → ProlongationTuple.IsCuspidal P V)
    (hsplit : ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), ProlongationTuple.IsCuspidal P V →
      ProlongationTuple.IsInftySide P V ∨ ProlongationTuple.IsZeroSide P V)
    (hInftyNA : ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), ProlongationTuple.IsInftySide P V → ¬ IsAffineGeomPlace (ResidueField A) N (P.reduceFst V))
    (hInftyNA' : ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), ProlongationTuple.IsInftySide P V → ¬ IsAffineGeomPlace (ResidueField A) N (P.reduceSnd V))
    (hZeroNA : ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), ProlongationTuple.IsZeroSide P V → ¬ IsAffineGeomPlace (ResidueField A) N (P.reduceSnd V))
    (hZeroNA' : ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), ProlongationTuple.IsZeroSide P V → ¬ IsAffineGeomPlace (ResidueField A) N (P.reduceFst V))
    (hφaff : ∀ v : (Place (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) N)), IsAffineGeomPlace (ResidueField A) N v → IsAffineGeomPlace (ResidueField A) N (frobOnPlacesGeomLevel (ResidueField A) N data hKr v))

    (hNss : ∀ s ∈ nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W, s.1 ∈ ssPlaces q N (ResidueField A) ∧ s.2 ∈ ssPlaces q N (ResidueField A))

    (hzone : ∀ T : Finset (Place (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) N)), (∀ t ∈ T, t ∉ ssPlaces q N (ResidueField A)) →
      ∃ Z : Finset (Place (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) N)), (∀ v ∈ T, v ∈ Z) ∧ (∀ v ∈ T, frobOnPlacesGeomLevel (ResidueField A) N data hKr v ∈ Z) ∧ (∀ v, frobOnPlacesGeomLevel (ResidueField A) N data hKr v ∈ T → v ∈ Z) ∧
        (∀ v, ¬ IsAffineGeomPlace (ResidueField A) N v → v ∈ Z) ∧ (∀ v, frobOnPlacesGeomLevel (ResidueField A) N data hKr (frobOnPlacesGeomLevel (ResidueField A) N data hKr v) = v → v ∉ ssPlaces q N (ResidueField A) → v ∈ Z) ∧
        (∀ v ∈ Z, v ∉ ssPlaces q N (ResidueField A)))

    (hAUX : ∀ (B : Finset (Place (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) N))) (m₁ m₂ : ℕ),
      ∃ (Q₁ : Fin m₁ → Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) (Q₂ : Fin m₂ → Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))),
        (∀ i, P.IsStrictFst (Q₁ i)) ∧ (∀ j, P.IsStrictSnd (Q₂ j)) ∧
        (Function.Injective fun i => P.reduceFst (Q₁ i)) ∧ (Function.Injective fun j => P.reduceSnd (Q₂ j)) ∧
        (∀ i, P.reduceFst (Q₁ i) ∉ B) ∧ (∀ j, P.reduceSnd (Q₂ j) ∉ B))

    (hINTERP : ∀ (U Zv Za : Finset (Place (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) N))) (t₀ : (Place (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) N))) (β : (ResidueField A)) (val : (Place (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) N)) → (ResidueField A)) (bad : Finset (ResidueField A)),
      Disjoint U Zv → Disjoint U Za → Disjoint Zv Za → t₀ ∉ U → t₀ ∉ Zv → t₀ ∉ Za →
      Zv.card + 2 * genusFF (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) N) + 2 ≤ U.card →
      ∃ g : ↥(modularFunctionFieldC (ResidueField A) N), g ∈ riemannRochSpace (∑ u ∈ U, Finsupp.single u (1 : ℤ)) ∧
        t₀.ord (g - algebraMap (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) N) β) = 1 ∧ (∀ z ∈ Zv, z.HasValue g (val z)) ∧
        (∀ z ∈ Za, ∃ γ : (ResidueField A), γ ∉ bad ∧ z.HasValue g γ))

    (hREALN : ∀ (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))), 0 ≤ D → P.IsGoodDiv D →
      2 * (genusFF (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) N) : ℤ) - 1 + W.card ≤ (Finsupp.mapDomain P.reduceFst (P.fstDiv D)).degree →
      2 * (genusFF (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) N) : ℤ) - 1 ≤ (Finsupp.mapDomain P.reduceSnd (P.sndDiv D)).degree →
      ∀ (g₁ g₂ : ↥(modularFunctionFieldFullC (ResidueField A) N)),
        (R.ι g₁ : ↥(modularFunctionFieldC (ResidueField A) N)) ∈ riemannRochSpace (Finsupp.mapDomain P.reduceFst (P.fstDiv D)) →
        (R.ι g₂ : ↥(modularFunctionFieldC (ResidueField A) N)) ∈ riemannRochSpace (Finsupp.mapDomain P.reduceSnd (P.sndDiv D)) →
        (∀ s ∈ nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W, ∃ c : (ResidueField A),
          s.1.HasValue (R.ι g₁ : ↥(modularFunctionFieldC (ResidueField A) N)) c ∧ s.2.HasValue (R.ι g₂ : ↥(modularFunctionFieldC (ResidueField A) N)) c) →
        ∃ (G : ↥(modularFunctionFieldBar (N * q))) (h₁ : G ∈ R.R₁.integers) (h₂ : G ∈ R.R₂.integers),
          G ∈ riemannRochSpace D ∧ R.R₁.residue ⟨G, h₁⟩ = g₁ ∧ R.R₂.residue ⟨G, h₂⟩ = g₂)

    (toFull : ↥(modularFunctionFieldC (ResidueField A) N) → ↥(modularFunctionFieldFullC (ResidueField A) N)) (ι_toFull : ∀ g : ↥(modularFunctionFieldC (ResidueField A) N), R.ι (toFull g) = g)

    (T : Finset (Place (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) N))) (hT : ∀ t ∈ T, t ∉ ssPlaces q N (ResidueField A))
    (V₀ : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) (hV₀ : P.reduceFst V₀ ∈ T ∨ P.reduceSnd V₀ ∈ T) :
    ∃ (Z : Finset (Place (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) N))) (f : ↥(modularFunctionFieldBar (N * q))) (h₁ : f ∈ R.R₁.integers) (h₂ : f ∈ R.R₂.integers)
      (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))),

      ((∀ v ∈ T, v ∈ Z) ∧ (∀ v, ¬ IsAffineGeomPlace (ResidueField A) N v → v ∈ Z) ∧
        (∀ v, frobOnPlacesGeomLevel (ResidueField A) N data hKr (frobOnPlacesGeomLevel (ResidueField A) N data hKr v) = v → v ∉ ssPlaces q N (ResidueField A) → v ∈ Z) ∧ (∀ v ∈ Z, v ∉ ssPlaces q N (ResidueField A))) ∧
      f ≠ 0 ∧ R.residue₁ ⟨f, h₁⟩ ≠ 0 ∧ R.residue₂ ⟨f, h₂⟩ ≠ 0 ∧
      (∀ V, D V = V.ord f) ∧ D V₀ = 1 ∧
      (∀ V, D V < 0 → (P.IsStrictFst V ∧ P.reduceFst V ∉ Z) ∨ (P.IsStrictSnd V ∧ P.reduceSnd V ∉ Z)) ∧

      (∀ z, (z ∈ Z ∨ z ∈ W) → z ≠ P.reduceFst V₀ → z.ord (R.residue₁ ⟨f, h₁⟩) = 0) ∧
      (∀ z, (z ∈ Z ∨ z ∈ W) → z ≠ P.reduceSnd V₀ → z.ord (R.residue₂ ⟨f, h₂⟩) = 0) ∧
      (((P.reduceFst V₀).ord (R.residue₁ ⟨f, h₁⟩) = 1 ∧ (P.reduceSnd V₀).ord (R.residue₂ ⟨f, h₂⟩) = 0) ∨
        ((P.reduceFst V₀).ord (R.residue₁ ⟨f, h₁⟩) = 0 ∧ (P.reduceSnd V₀).ord (R.residue₂ ⟨f, h₂⟩) = 1)) ∧
      (∀ V, V ≠ V₀ → 1 ≤ D V → P.reduceFst V ∈ Z → P.reduceSnd V ∈ Z → False) ∧
      ∀ V ∈ D.support, V ≠ V₀ → P.reduceFst V ∉ T ∧ P.reduceSnd V ∉ T := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_commonUnit_ord_eq_one_orderTables_of_realisation.solution
