import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_AdelicIndex
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Divisor_mem_principal_of_forall_ell_pos_add
set_option autoImplicit false

universe u v

open AlgebraicCurve

theorem AlgebraicCurve.Divisor.mem_principal_of_forall_ell_pos_add
    {K : Type u} {F : Type v} [Field K] [Field F] [Algebra K F] [IsAlgClosed K]
    [IsCurveOver K F] [Algebra.EssFiniteType K F] (Kc : Divisor K F) (g : ℕ)
    (hRR : ∀ D : Divisor K F, (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1 - g)
    (ξ : Divisor K F) (hξ : Divisor.degree ξ = 0)
    (h : ∀ D : Divisor K F, Divisor.degree D = (g : ℤ) - 1 → 0 < ell D → 0 < ell (D + ξ)) :
    ξ ∈ Divisor.principal (K := K) (F := F) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Divisor_mem_principal_of_forall_ell_pos_add.solution
