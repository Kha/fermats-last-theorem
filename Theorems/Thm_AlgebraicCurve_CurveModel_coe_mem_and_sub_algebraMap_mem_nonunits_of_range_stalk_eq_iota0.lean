import Mathlib
import Definitions.Def_AlgebraicCurve_CurveModelConstruction
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_CurveModel_coe_mem_and_sub_algebraMap_mem_nonunits_of_range_stalk_eq_iota0

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry IntermediateField AlgebraicCurve AlgebraicCurve.CurveModel

universe u

theorem AlgebraicCurve.CurveModel.coe_mem_and_sub_algebraMap_mem_nonunits_of_range_stalk_eq_iota0
    (K : Type u) [Field K] {L : Type u} [Field L] [Algebra K L] (t : L) [Fact (t ≠ 0)]
    [FiniteDimensional ↥K⟮t⟯ L]
    (P : closedPoints (glued K t) → Place K L)
    (hPst : ∀ x : closedPoints (glued K t),
      (((gluedFunctionFieldEquiv K t).symm : (glued K t).functionField ≃+* L).toRingHom.comp
          (algebraMap ((glued K t).presheaf.stalk x.1) (glued K t).functionField)).range =
        (P x).toValuationSubring.toSubring)
    (χ : ↥(chartRing K ({t} : Set L)) →ₐ[K] K)
    (z : closedPoints (glued K t))
    (hz : z.1 = (ι₀ K t).base ((Spec.map (CommRingCat.ofHom χ.toRingHom)).base
      (IsLocalRing.closedPoint K))) :
    ∀ c : ↥(chartRing K ({t} : Set L)),
      (c : L) ∈ (P z).toValuationSubring ∧
        (c : L) - algebraMap K L (χ c) ∈ (P z).toValuationSubring.nonunits := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_CurveModel_coe_mem_and_sub_algebraMap_mem_nonunits_of_range_stalk_eq_iota0.solution
