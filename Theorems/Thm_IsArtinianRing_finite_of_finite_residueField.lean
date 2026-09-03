import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.RingTheory.Ideal.Quotient.Index
import Mathlib.RingTheory.LocalRing.ResidueField.Defs
import P2M.Util
import P2M.Sol.S_IsArtinianRing_finite_of_finite_residueField

theorem IsArtinianRing.finite_of_finite_residueField (R : Type*) [CommRing R] [IsArtinianRing R] [IsLocalRing R] [Finite (IsLocalRing.ResidueField R)] :
    Finite R := by p2m_exact_reverting @_root_.P2MW.S_IsArtinianRing_finite_of_finite_residueField.solution
