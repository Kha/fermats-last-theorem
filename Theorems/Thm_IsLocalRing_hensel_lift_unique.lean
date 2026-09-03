import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_DivisorPushPull
import Definitions.Def_DedekindDomain_AdicValuation_InlineSpecific
import Definitions.Def_AlgebraicCurve_PlaceCompletion
import P2M.Util
import P2M.Sol.S_IsLocalRing_hensel_lift_unique

open Polynomial IsLocalRing in
theorem IsLocalRing.hensel_lift_unique {R : Type*} [CommRing R] [IsLocalRing R] {f : Polynomial R} {a b : R}
    (ha : f.IsRoot a) (hb : f.IsRoot b) (hmem : b - a ∈ IsLocalRing.maximalIdeal R)
    (hunit : IsUnit (f.derivative.eval a)) : a = b := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_hensel_lift_unique.solution
