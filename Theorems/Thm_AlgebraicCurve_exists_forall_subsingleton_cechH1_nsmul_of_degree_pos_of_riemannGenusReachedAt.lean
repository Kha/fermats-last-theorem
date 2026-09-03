import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicGeometry_TwoChartCech
import Definitions.Def_AlgebraicCurve_CechSectionsOfDivisor
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_exists_forall_subsingleton_cechH1_nsmul_of_degree_pos_of_riemannGenusReachedAt

set_option autoImplicit false

p2m_open "AlgebraicCurve~cechRiemannRoch_of_genusReached~cechH1ToH1_bijective"

theorem AlgebraicCurve.exists_forall_subsingleton_cechH1_nsmul_of_degree_pos_of_riemannGenusReachedAt
    {K F : Type*} [Field K] [Field F] [Algebra K F] [IsCurveOver K F]
    [FiniteDimensional K ↥(riemannRochSpace (0 : Divisor K F))]
    {γ : ℤ} {D₀ : Divisor K F} (hγ : RiemannGenusReachedAt γ D₀)
    {S₀ S₁ : Set (Place K F)} (hcover : S₀ ∪ S₁ = Set.univ) (h₀ : ∃ v, v ∉ S₀) (h₁ : ∃ v, v ∉ S₁)
    (D : Divisor K F) (hD : 0 < Divisor.degree D) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Subsingleton (cechH1 S₀ S₁ ((n : ℤ) • D)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_exists_forall_subsingleton_cechH1_nsmul_of_degree_pos_of_riemannGenusReachedAt.solution
