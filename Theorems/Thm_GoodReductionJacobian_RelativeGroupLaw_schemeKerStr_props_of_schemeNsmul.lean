import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_schemeKerStr_props_of_schemeNsmul

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing TensorProduct

theorem GoodReductionJacobian.RelativeGroupLaw.schemeKerStr_props_of_schemeNsmul
    {R : Type u} [CommRing R] {G : Scheme.{u}} (g : G ⟶ Spec (CommRingCat.of R)) [IsSeparated g] [QuasiCompact g]
    (L : RelativeGroupLaw R g) (n : ℕ)
    (hqf : LocallyQuasiFinite (L.schemeNsmul n)) (hfl : Flat (L.schemeNsmul n)) :
    LocallyQuasiFinite (L.schemeKerStr n) ∧ QuasiCompact (L.schemeKerStr n) ∧ Flat (L.schemeKerStr n) ∧
      IsSeparated (L.schemeKerStr n) ∧
      IsClosedImmersion (L.one (𝟙 (Spec (CommRingCat.of R)))).1 ∧
      IsClosedImmersion (pullback.fst (L.schemeNsmul n) (L.one (𝟙 (Spec (CommRingCat.of R)))).1) ∧
      (Smooth g → LocallyOfFiniteType g) := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_schemeKerStr_props_of_schemeNsmul.solution
