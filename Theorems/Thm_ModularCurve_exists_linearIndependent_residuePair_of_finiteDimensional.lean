import Mathlib
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_ModularCurve_CharPReduction
import Definitions.Def_ModularCurve_CuspidalClass
import Definitions.Def_ModularCurve_X0ModL
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_linearIndependent_residuePair_of_finiteDimensional

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open AlgebraicCurve IsLocalRing ModularCurve
theorem ModularCurve.exists_linearIndependent_residuePair_of_finiteDimensional
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    (R₁ R₂ : RegularProlongation A (modularFunctionFieldBar (1 * q))
      (modularFunctionFieldFullC (ResidueField A) 1))
    (h₁ : ∀ (y : LaurentSeries A) (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar (1 * q)),
      ∃ h : (⟨coeffMap A.subtype y, hy⟩ : modularFunctionFieldBar (1 * q)) ∈ R₁.integers,
        ((R₁.residue ⟨_, h⟩ : modularFunctionFieldFullC (ResidueField A) 1) :
            LaurentSeries (ResidueField A)) = coeffMap (IsLocalRing.residue A) y)
    (h₂ : ∀ f : modularFunctionFieldBar (1 * q),
      f ∈ R₂.integers ↔ frickeInvolutionBar (1 * q) f ∈ R₁.integers)
    (h₂' : ∀ (f : modularFunctionFieldBar (1 * q)) (h : f ∈ R₂.integers),
      R₂.residue ⟨f, h⟩ = R₁.residue ⟨frickeInvolutionBar (1 * q) f, (h₂ f).mp h⟩)
    (V : Submodule (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)))
    [FiniteDimensional (AlgebraicClosure ℚ) V]
    (hint : ∃ b : Fin (Module.finrank (AlgebraicClosure ℚ) V) → modularFunctionFieldBar (1 * q),
      (∀ i, b i ∈ V) ∧ LinearIndependent (AlgebraicClosure ℚ) b ∧
      ∀ i, (∃ (c : AlgebraicClosure ℚ) (y : LaurentSeries A), c ≠ 0 ∧
              coeffMap A.subtype y = c • ((b i : modularFunctionFieldBar (1 * q)) :
                LaurentSeries (AlgebraicClosure ℚ))) ∧
           (∃ (c : AlgebraicClosure ℚ) (y : LaurentSeries A), c ≠ 0 ∧
              coeffMap A.subtype y = c • ((frickeInvolutionBar (1 * q) (b i) :
                modularFunctionFieldBar (1 * q)) : LaurentSeries (AlgebraicClosure ℚ)))) :
    ∃ (G : Fin (Module.finrank (AlgebraicClosure ℚ) V) → modularFunctionFieldBar (1 * q))
      (hG₁ : ∀ i, G i ∈ R₁.integers) (hG₂ : ∀ i, G i ∈ R₂.integers),
      (∀ i, G i ∈ V) ∧
      LinearIndependent (ResidueField A)
        (fun i => (R₁.residue ⟨G i, hG₁ i⟩, R₂.residue ⟨G i, hG₂ i⟩)) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_linearIndependent_residuePair_of_finiteDimensional.solution
