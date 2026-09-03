import Mathlib
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_KatzLevelPCusps
import P2M.Util
import P2M.Sol.S_ModularCurve_cuspData_map_coeffMap

theorem ModularCurve.cuspData_map_coeffMap {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (p : ℕ) [Fact p.Prime] (hp : IsUnit (p : R)) (ζ : Rˣ)
    (hζ : ∑ i ∈ Finset.range p, (ζ : R) ^ i = 0) (v w : Fin 2 → ZMod p) :
    (ModularCurve.cuspData R p ζ v w).map (ModularCurve.coeffMap f) =
      ModularCurve.cuspData S p (Units.map (f : R →* S) ζ) v w := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_cuspData_map_coeffMap.solution
