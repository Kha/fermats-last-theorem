import Mathlib.RingTheory.DedekindDomain.SInteger
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import P2M.Util
import P2M.Sol.S_M4aHerbrand_finrank_sUnit_eq_univ

set_option autoImplicit false
open IsDedekindDomain NumberField

theorem M4aHerbrand.finrank_sUnit_eq_univ (K : Type*) [Field K] [NumberField K]
    (S : Set (HeightOneSpectrum (𝓞 K))) [Finite S] :
    Module.Finite ℤ (Additive (S.unit K)) ∧
    Module.finrank ℤ (Additive (S.unit K)) = Nat.card S + NumberField.Units.rank K := by p2m_exact_reverting @_root_.P2MW.S_M4aHerbrand_finrank_sUnit_eq_univ.solution
