import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_AlgebraicGeometry_RelativeGroupLawEndDegree
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_endDegree_inv_idPoint_eq_one_and_inv_eq_schemeHomOverComp_inv_idPoint
attribute [-instance] instTopologicallyFGOfFiniteType
attribute [-simp] RegularLocalRingQuotientAscent.dualNumberFst_apply

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.endDegree_inv_idPoint_eq_one_and_inv_eq_schemeHomOverComp_inv_idPoint
    (K : Type u) [Field K] [IsAlgClosed K] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of K))
    (L : RelativeGroupLaw K f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle K f)
    (g : ℕ) [SmoothOfRelativeDimension g f] :
    letI := L.pointCommGroup hc f
    L.endDegree (RelativeGroupLaw.idPoint : SchemeHomOver f f)⁻¹ = 1 ∧
      (∀ β : SchemeHomOver f f,
        β⁻¹ = NeronModelInfra.schemeHomOverComp β (RelativeGroupLaw.idPoint : SchemeHomOver f f)⁻¹) ∧
      ∀ (β : SchemeHomOver f f),
        (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (x y : SchemeHomOver t f),
          NeronModelInfra.schemeHomOverComp (L.mul t x y) β =
            L.mul t (NeronModelInfra.schemeHomOverComp x β) (NeronModelInfra.schemeHomOverComp y β)) →
        L.endDegree β ≠ 0 →
        L.endDegree (NeronModelInfra.schemeHomOverComp β (RelativeGroupLaw.idPoint : SchemeHomOver f f)⁻¹) = L.endDegree β := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_endDegree_inv_idPoint_eq_one_and_inv_eq_schemeHomOverComp_inv_idPoint.solution
