import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_AdmissibleAlgebra_fixedPoints_isAdicComplete_and_finite_and_finiteType

set_option autoImplicit false

theorem AlgebraicGeometry.AdmissibleAlgebra.fixedPoints_isAdicComplete_and_finite_and_finiteType
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
    (π : 𝒪) (hπ : Irreducible π) (hcomplete : IsAdicComplete (Ideal.span {π}) 𝒪)
    (R : Type) [CommRing R] [Algebra 𝒪 R]
    (hRc : IsAdicComplete (Ideal.span {algebraMap 𝒪 R π}) R)
    (hRtf : ∀ x : R, algebraMap 𝒪 R π * x = 0 → x = 0)
    (hRft : Algebra.FiniteType 𝒪 (R ⧸ Ideal.span {algebraMap 𝒪 R π}))
    (G : Type) [Group G] [Finite G] [MulSemiringAction G R] [SMulCommClass G 𝒪 R] :
    IsAdicComplete (Ideal.span {algebraMap 𝒪 (↥(FixedPoints.subalgebra 𝒪 R G)) π}) ↥(FixedPoints.subalgebra 𝒪 R G) ∧
    Module.Finite ↥(FixedPoints.subalgebra 𝒪 R G) R ∧
    Algebra.FiniteType 𝒪 (↥(FixedPoints.subalgebra 𝒪 R G) ⧸ Ideal.span {algebraMap 𝒪 (↥(FixedPoints.subalgebra 𝒪 R G)) π}) ∧
    (∀ k : ℕ, ∀ x : ↥(FixedPoints.subalgebra 𝒪 R G),
      (x : R) ∈ Ideal.span {(algebraMap 𝒪 R π) ^ k} → x ∈ Ideal.span {(algebraMap 𝒪 (↥(FixedPoints.subalgebra 𝒪 R G)) π) ^ k}) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_AdmissibleAlgebra_fixedPoints_isAdicComplete_and_finite_and_finiteType.solution
