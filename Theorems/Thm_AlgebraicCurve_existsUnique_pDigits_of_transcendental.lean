import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.Perfect
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_existsUnique_pDigits_of_transcendental

theorem AlgebraicCurve.existsUnique_pDigits_of_transcendental {K M : Type*} [Field K] [Field M] [Algebra K M]
    [PerfectField K] (p : ℕ) [hp : Fact p.Prime] [CharP K p] (t : M) (htr : Transcendental K t)
    [FiniteDimensional (IntermediateField.adjoin K ({t} : Set M)) M] (htp : ∀ a : M, a ^ p ≠ t) (g : M) :
    ∃! a : Fin p → M, g = ∑ i : Fin p, a i ^ p * t ^ (i : ℕ) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_existsUnique_pDigits_of_transcendental.solution
