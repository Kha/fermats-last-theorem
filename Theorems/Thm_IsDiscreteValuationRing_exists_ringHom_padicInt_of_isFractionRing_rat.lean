import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Localization.FractionRing
import P2M.Util
import P2M.Sol.S_IsDiscreteValuationRing_exists_ringHom_padicInt_of_isFractionRing_rat

theorem IsDiscreteValuationRing.exists_ringHom_padicInt_of_isFractionRing_rat
    (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Algebra R ℚ] [IsFractionRing R ℚ]
    (p : ℕ) [Fact p.Prime] (hp : Irreducible (p : R)) :
    ∃ f : R →+* ℤ_[p], ∀ r : R, ((f r : ℤ_[p]) : ℚ_[p]) = (algebraMap ℚ ℚ_[p]) (algebraMap R ℚ r) := by p2m_exact_reverting @_root_.P2MW.S_IsDiscreteValuationRing_exists_ringHom_padicInt_of_isFractionRing_rat.solution
