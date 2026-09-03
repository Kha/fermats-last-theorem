import Mathlib
import P2M.Util
import P2M.Sol.S_IsLocalRing_of_isDomain_of_moduleFinite_of_isAdicComplete

theorem IsLocalRing.of_isDomain_of_moduleFinite_of_isAdicComplete (R : Type*) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (IsLocalRing.maximalIdeal R) R] (D : Type*) [CommRing D] [IsDomain D] [Algebra R D] [Module.Finite R D] : IsLocalRing D := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_of_isDomain_of_moduleFinite_of_isAdicComplete.solution
