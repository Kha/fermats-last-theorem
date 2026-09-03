import Definitions.Def_ModularCurve_ProlongationTuple
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_linearIndependent_residuePair_forall_arithmeticGalois_smul_eq_of_finiteDimensional_mul

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve

theorem ModularCurve.exists_linearIndependent_residuePair_forall_arithmeticGalois_smul_eq_of_finiteDimensional_mul
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ}
    (R₁ R₂ : RegularProlongation A (modularFunctionFieldBar (N * q))
      (modularFunctionFieldFullC (ResidueField A) N))
    (h₁ : ∀ (y : LaurentSeries A) (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar (N * q)),
      ∃ h : (⟨coeffMap A.subtype y, hy⟩ : modularFunctionFieldBar (N * q)) ∈ R₁.integers,
        ((R₁.residue ⟨_, h⟩ : modularFunctionFieldFullC (ResidueField A) N) :
            LaurentSeries (ResidueField A)) = coeffMap (IsLocalRing.residue A) y)
    (h₂ : ∀ f : modularFunctionFieldBar (N * q),
      f ∈ R₂.integers ↔ PlaceSpecialization.ProlongationTuple.atkinLehnerBar N q f ∈ R₁.integers)
    (h₂' : ∀ (f : modularFunctionFieldBar (N * q)) (h : f ∈ R₂.integers),
      R₂.residue ⟨f, h⟩ =
        R₁.residue ⟨PlaceSpecialization.ProlongationTuple.atkinLehnerBar N q f, (h₂ f).mp h⟩)
    (S : Set (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (V : Submodule (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
    [FiniteDimensional (AlgebraicClosure ℚ) V]
    (hint : ∃ b : Fin (Module.finrank (AlgebraicClosure ℚ) V) → modularFunctionFieldBar (N * q),
      (∀ i, b i ∈ V) ∧ LinearIndependent (AlgebraicClosure ℚ) b ∧
      (∀ i, (∃ (c : AlgebraicClosure ℚ) (y : LaurentSeries A), c ≠ 0 ∧
              coeffMap A.subtype y = c • ((b i : modularFunctionFieldBar (N * q)) :
                LaurentSeries (AlgebraicClosure ℚ))) ∧
           (∃ (c : AlgebraicClosure ℚ) (y : LaurentSeries A), c ≠ 0 ∧
              coeffMap A.subtype y = c • ((PlaceSpecialization.ProlongationTuple.atkinLehnerBar N q (b i) :
                modularFunctionFieldBar (N * q)) : LaurentSeries (AlgebraicClosure ℚ)))) ∧
      ∀ i, ∀ σ ∈ S, arithmeticGalois (modularFunctionFieldFull (N * q)) σ • b i = b i) :
    ∃ (G : Fin (Module.finrank (AlgebraicClosure ℚ) V) → modularFunctionFieldBar (N * q))
      (hG₁ : ∀ i, G i ∈ R₁.integers) (hG₂ : ∀ i, G i ∈ R₂.integers),
      (∀ i, G i ∈ V) ∧
      LinearIndependent (ResidueField A)
        (fun i => (R₁.residue ⟨G i, hG₁ i⟩, R₂.residue ⟨G i, hG₂ i⟩)) ∧
      ∀ i, ∀ σ ∈ S, arithmeticGalois (modularFunctionFieldFull (N * q)) σ • G i = G i := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_linearIndependent_residuePair_forall_arithmeticGalois_smul_eq_of_finiteDimensional_mul.solution
