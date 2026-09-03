import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_AdelicIndex
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_RROpens_exists_effective_sub_add_smul_single_mem_principal

universe u v

open AlgebraicCurve

theorem AlgebraicCurve.RROpens.exists_effective_sub_add_smul_single_mem_principal
    {K : Type u} {F : Type v} [Field K] [Field F] [Algebra K F] [HasPrincipalDivisors K F]
    (g : ℕ) (Kc : Divisor K F)
    (hRR : ∀ D : Divisor K F, (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1 - g)
    (P : Place K F) (hP : P.deg = 1) (A : Divisor K F) (hA : Divisor.degree A = 0) :
    ∃ E : Divisor K F, (∀ v, 0 ≤ E v) ∧
      E - (A + (g : ℤ) • Finsupp.single P 1) ∈ Divisor.principal (K := K) (F := F) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_RROpens_exists_effective_sub_add_smul_single_mem_principal.solution
