import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawFibre
import Definitions.Def_AlgebraicGeometry_SchemeFibreEndo
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_abelianSchemePropertyBundle_fibreStr

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u
theorem GoodReductionJacobian.abelianSchemePropertyBundle_fibreStr
    {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (hA : AbelianSchemePropertyBundle R f) (s : (Spec (CommRingCat.of R) : Scheme.{u})) :
    AbelianSchemePropertyBundle (RelativeGroupLaw.baseResidueField s) (RelativeGroupLaw.fibreStr f s) := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_abelianSchemePropertyBundle_fibreStr.solution
