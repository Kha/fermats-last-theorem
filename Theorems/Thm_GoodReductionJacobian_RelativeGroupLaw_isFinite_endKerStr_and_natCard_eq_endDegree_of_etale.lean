import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_AlgebraicGeometry_RelativeGroupLawEndDegree
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_isFinite_endKerStr_and_natCard_eq_endDegree_of_etale

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.isFinite_endKerStr_and_natCard_eq_endDegree_of_etale
    (K : Type u) [Field K] [IsAlgClosed K] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of K))
    [IsProper f]
    (L : RelativeGroupLaw K f) (β : SchemeHomOver f f) [Etale (L.endKerStr β)] :
    IsFinite (L.endKerStr β) ∧
      Finite {x : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) f //
        NeronModelInfra.schemeHomOverComp x β = L.one (𝟙 (Spec (CommRingCat.of K)))} ∧
      Nat.card {x : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) f //
        NeronModelInfra.schemeHomOverComp x β = L.one (𝟙 (Spec (CommRingCat.of K)))} = L.endDegree β := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_isFinite_endKerStr_and_natCard_eq_endDegree_of_etale.solution
