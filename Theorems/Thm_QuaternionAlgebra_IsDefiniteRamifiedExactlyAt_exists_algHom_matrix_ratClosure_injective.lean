import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_ValuationSubring_CompletionRatClosure
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_IsDefiniteRamifiedExactlyAt_exists_algHom_matrix_ratClosure_injective
attribute [-simp] QuaternionAlgebra.nrd_coe QuaternionAlgebra.nrd_one QuaternionAlgebra.trd_mk QuaternionAlgebra.nrd_mk QuaternionAlgebra.nrd_neg QuaternionAlgebra.nrd_zero QuaternionAlgebra.nrd_star QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul

set_option autoImplicit false

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField

theorem QuaternionAlgebra.IsDefiniteRamifiedExactlyAt.exists_algHom_matrix_ratClosure_injective
    {a b : ℚ} {q : ℕ} [Fact q.Prime] (hdef : QuaternionAlgebra.IsDefiniteRamifiedExactlyAt a b q)
    {r : ℕ} [Fact r.Prime] (hrq : r ≠ q)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime r) :
    ∃ ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ↥(ValuationSubring.ratClosure A), Function.Injective ι := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_IsDefiniteRamifiedExactlyAt_exists_algHom_matrix_ratClosure_injective.solution
