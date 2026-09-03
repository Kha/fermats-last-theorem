import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Mathlib
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_isAffine_schemeKer_of_locallyQuasiFinite

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem GoodReductionJacobian.RelativeGroupLaw.isAffine_schemeKer_of_locallyQuasiFinite
    {R : Type u} [CommRing R] [IsNoetherianRing R] (hR : ringKrullDim R ≤ 1)
    {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} [IsSeparated f] [LocallyOfFiniteType f]
    (G : RelativeGroupLaw R f) (n : ℕ) [LocallyQuasiFinite (G.schemeKerStr n)] [QuasiCompact (G.schemeKerStr n)] :
    IsAffine (G.schemeKer n) := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_isAffine_schemeKer_of_locallyQuasiFinite.solution
