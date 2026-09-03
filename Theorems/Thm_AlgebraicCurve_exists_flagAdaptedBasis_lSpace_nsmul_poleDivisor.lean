import Mathlib
import Definitions.Def_AlgebraicCurve_AdelicIndex
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_exists_flagAdaptedBasis_lSpace_nsmul_poleDivisor

set_option autoImplicit false

open AlgebraicCurve hiding mul_mem_lSpace_nsmul_succ_and_reflects_of_poleDivisor

theorem AlgebraicCurve.exists_flagAdaptedBasis_lSpace_nsmul_poleDivisor
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (x : F) (hx : Transcendental K x)
    (D : Divisor K F) (hD : ∀ v : Place K F, D v = max 0 (-v.ord x))
    (hFD : ∀ M : ℕ, FiniteDimensional K ↥(LSpace (M • D)))
    (hell0 : ell (0 : Divisor K F) = 1)
    (M₀ d g₀ : ℕ) (hd : 1 ≤ d)
    (hell : ∀ N, M₀ ≤ N → (ell (N • D) : ℤ) = N * d + 1 - g₀) :
    ∃ (d' : ℕ) (y : Fin d' → F) (e : Fin d' → ℕ),
      (∀ M : ℕ, (LSpace (M • D) : Submodule K F)
        ≤ Submodule.span K {z | ∃ σ j, j + e σ ≤ M ∧ z = x ^ j * y σ}) ∧
      LinearIndependent K (fun p : Fin d' × ℕ => x ^ p.2 * y p.1) ∧
      (∀ σ, y σ ∈ LSpace ((e σ) • D)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_exists_flagAdaptedBasis_lSpace_nsmul_poleDivisor.solution
