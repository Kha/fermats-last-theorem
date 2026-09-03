import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_AdelicIndex
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_exists_forall_adicValuation_sub_le_of_riemannGenusReachedAt

namespace AlgebraicCurve
theorem exists_forall_adicValuation_sub_le_of_riemannGenusReachedAt {K F : Type*} [Field K] [Field F] [Algebra K F] [IsCurveOver K F]
    [FiniteDimensional K ↥(LSpace (0 : Divisor K F))]
    {γ : ℤ} {D₀ : Divisor K F} (h : RiemannGenusReachedAt γ D₀)
    (S : Set (Place K F)) {v₀ : Place K F} (hv₀ : v₀ ∉ S) (D : Divisor K F)
    (α : Place K F → F) (hα : {v | v ∈ S ∧ ¬ v.adicValuation (α v) ≤ WithZero.exp (D v)}.Finite) :
    ∃ f : F, ∀ v ∈ S, v.adicValuation (α v - f) ≤ WithZero.exp (D v) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_exists_forall_adicValuation_sub_le_of_riemannGenusReachedAt.solution
end AlgebraicCurve
