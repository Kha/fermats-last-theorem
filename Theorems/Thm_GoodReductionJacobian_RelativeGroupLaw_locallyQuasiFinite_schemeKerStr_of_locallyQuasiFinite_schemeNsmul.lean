import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_locallyQuasiFinite_schemeKerStr_of_locallyQuasiFinite_schemeNsmul

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem GoodReductionJacobian.RelativeGroupLaw.locallyQuasiFinite_schemeKerStr_of_locallyQuasiFinite_schemeNsmul
    {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (G : RelativeGroupLaw R f) (n : ℕ) [LocallyQuasiFinite (G.schemeNsmul n)] :
    LocallyQuasiFinite (G.schemeKerStr n) := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_locallyQuasiFinite_schemeKerStr_of_locallyQuasiFinite_schemeNsmul.solution
