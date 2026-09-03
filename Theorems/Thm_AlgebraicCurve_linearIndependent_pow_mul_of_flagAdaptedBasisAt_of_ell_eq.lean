import Mathlib
import Definitions.Def_AlgebraicCurve_AdelicIndex
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_linearIndependent_pow_mul_of_flagAdaptedBasisAt_of_ell_eq

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.linearIndependent_pow_mul_of_flagAdaptedBasisAt_of_ell_eq
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (x : F) (D : Divisor K F) (hD : ∀ v : Place K F, D v = max 0 (-v.ord x))
    (hFD : ∀ M : ℕ, FiniteDimensional K ↥(LSpace (M • D)))
    (M₀ d g₀ : ℕ)
    (hell : ∀ N, M₀ ≤ N → (ell (N • D) : ℤ) = N * d + 1 - g₀)
    {d' : ℕ} (y : Fin d' → F) (e : Fin d' → ℕ)
    (hle : ∀ σ, e σ ≤ M₀ + 1) (hy : ∀ σ, y σ ∈ LSpace ((e σ) • D))
    (hspan : ∀ M : ℕ, (LSpace (M • D) : Submodule K F)
      ≤ Submodule.span K {z | ∃ σ j, j + e σ ≤ M ∧ z = x ^ j * y σ})
    (hLIat : ∀ M ≤ M₀ + 1, LinearIndependent K
      (fun p : {p : Fin d' × ℕ // p.2 + e p.1 ≤ M} => x ^ p.val.2 * y p.val.1)) :
    LinearIndependent K (fun p : Fin d' × ℕ => x ^ p.2 * y p.1) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_linearIndependent_pow_mul_of_flagAdaptedBasisAt_of_ell_eq.solution
