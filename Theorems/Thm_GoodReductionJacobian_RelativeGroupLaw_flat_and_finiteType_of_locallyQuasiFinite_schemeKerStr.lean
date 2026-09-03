import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Mathlib
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_flat_and_finiteType_of_locallyQuasiFinite_schemeKerStr

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem GoodReductionJacobian.RelativeGroupLaw.flat_and_finiteType_of_locallyQuasiFinite_schemeKerStr
    {R : Type u} [CommRing R] [IsNoetherianRing R] (hR : ringKrullDim R ≤ 1)
    {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} [IsSeparated f] [LocallyOfFiniteType f]
    (G : RelativeGroupLaw R f) (n : ℕ) [LocallyQuasiFinite (G.schemeKerStr n)] [QuasiCompact (G.schemeKerStr n)]
    [Flat (G.schemeKerStr n)] :
    ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (G.schemeKerStr n).appTop).hom.Flat ∧
    ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (G.schemeKerStr n).appTop).hom.FiniteType := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_flat_and_finiteType_of_locallyQuasiFinite_schemeKerStr.solution
