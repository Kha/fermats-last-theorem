import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_AlgebraicGeometry_RelativeGroupLawEndDegree
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_etale_endKerStr_endAeval_of_map_maximalIdeal_le_sq

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.etale_endKerStr_endAeval_of_map_maximalIdeal_le_sq
    (K : Type u) [Field K] [IsAlgClosed K] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of K))
    (L : RelativeGroupLaw K f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle K f)
    (π : SchemeHomOver f f)
    (hdπ : ∀ x : A, (IsLocalRing.maximalIdeal (A.presheaf.stalk (π.1.base x))).map (π.1.stalkMap x).hom ≤
      IsLocalRing.maximalIdeal (A.presheaf.stalk x) ^ 2)
    (G : Polynomial ℤ) (hG : ((G.coeff 0 : ℤ) : K) ≠ 0) :
    Etale (L.endKerStr (L.endAeval hc π G)) := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_etale_endKerStr_endAeval_of_map_maximalIdeal_le_sq.solution
