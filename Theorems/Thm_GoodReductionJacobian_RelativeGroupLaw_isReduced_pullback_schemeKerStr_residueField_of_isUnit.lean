import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_isReduced_pullback_schemeKerStr_residueField_of_isUnit

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.isReduced_pullback_schemeKerStr_residueField_of_isUnit
    {R : Type u} [CommRing R] [IsLocalRing R]
    {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} [LocallyOfFiniteType f]
    (G : RelativeGroupLaw R f)
    (hcomm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
      G.mul t x y = G.mul t y x)
    (n : ℕ) (hn : IsUnit (n : R)) :
    IsReduced (pullback (G.schemeKerStr n)
      (Spec.map (CommRingCat.ofHom (algebraMap R (IsLocalRing.ResidueField R))))) := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_isReduced_pullback_schemeKerStr_residueField_of_isUnit.solution
