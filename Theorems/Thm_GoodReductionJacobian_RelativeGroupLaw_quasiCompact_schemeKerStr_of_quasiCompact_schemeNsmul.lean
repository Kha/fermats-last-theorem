import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_quasiCompact_schemeKerStr_of_quasiCompact_schemeNsmul

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem GoodReductionJacobian.RelativeGroupLaw.quasiCompact_schemeKerStr_of_quasiCompact_schemeNsmul
    {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (G : RelativeGroupLaw R f) (n : ℕ) [QuasiCompact (G.schemeNsmul n)] :
    QuasiCompact (G.schemeKerStr n) := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_quasiCompact_schemeKerStr_of_quasiCompact_schemeNsmul.solution
