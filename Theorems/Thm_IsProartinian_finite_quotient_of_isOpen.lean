import Mathlib
import Definitions.Def_Deformations_IsProartinian
import P2M.Util
import P2M.Sol.S_IsProartinian_finite_quotient_of_isOpen

universe u
theorem IsProartinian.finite_quotient_of_isOpen {R : Type u} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
  [IsLocalRing R] [IsProartinian R] [Finite (IsLocalRing.ResidueField R)] (I : Ideal R) (hI : IsOpen (I : Set R)) :
  Finite (R ⧸ I) := by p2m_exact_reverting @_root_.P2MW.S_IsProartinian_finite_quotient_of_isOpen.solution
