import Mathlib.FieldTheory.KrullTopology
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_AlgebraicClosure_stabilizer_primitiveRoot_three_le_of_isOpen_of_forall_inertia_inf_le
set_option autoImplicit false
open ValuationSubring
theorem AlgebraicClosure.stabilizer_primitiveRoot_three_le_of_isOpen_of_forall_inertia_inf_le
    {ζ : AlgebraicClosure ℚ} (hζ : IsPrimitiveRoot ζ 3)
    (N : Subgroup ((AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)))
    (hopen : IsOpen (N : Set ((AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ))))
    (hN : ∀ q : ℕ, q.Prime → ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime q →
      A.inertiaSubgroupIn ℚ ⊓
        MulAction.stabilizer ((AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)) ζ ≤ N) :
    MulAction.stabilizer ((AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)) ζ ≤ N := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicClosure_stabilizer_primitiveRoot_three_le_of_isOpen_of_forall_inertia_inf_le.solution
