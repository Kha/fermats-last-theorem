import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_AlgebraicGeometry_SchemeFibreEndo
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_flat_schemeNsmul_of_fibrewiseFlat
attribute [-instance] kmfloorsGlue_int_three_isPrime kmfloorsGlue_int_bot_isPrime

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
set_option maxHeartbeats 800000 in

theorem GoodReductionJacobian.RelativeGroupLaw.flat_schemeNsmul_of_fibrewiseFlat
    {R : Type} [CommRing R] [IsNoetherianRing R]
    {J : Scheme.{0}} {f : J ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    (hJ : AbelianSchemePropertyBundle R f) (n : ℕ) (hn : 0 < n)
    (hfib : ∀ s, Flat (schemeFibreEndo f (L.schemeNsmul n) (L.schemeNsmul_over n) s)) :
    Flat (L.schemeNsmul n) := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_flat_schemeNsmul_of_fibrewiseFlat.solution
