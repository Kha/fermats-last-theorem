import Mathlib
import Definitions.Def_AlgebraicCurve_AdelicIndex
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_exists_flagAdaptedBasisAt_lSpace_nsmul_poleDivisor

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.exists_flagAdaptedBasisAt_lSpace_nsmul_poleDivisor
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (x : F) (hx : Transcendental K x)
    (D : Divisor K F) (hD : ∀ v : Place K F, D v = max 0 (-v.ord x))
    (hFD : ∀ M : ℕ, FiniteDimensional K ↥(LSpace (M • D)))
    (hell0 : ell (0 : Divisor K F) = 1) (M₁ : ℕ) :
    ∃ (d' : ℕ) (y : Fin d' → F) (e : Fin d' → ℕ),
      (∀ σ, e σ ≤ M₁) ∧
      (∀ σ, y σ ∈ LSpace ((e σ) • D)) ∧
      (∀ M ≤ M₁, (LSpace (M • D) : Submodule K F)
        ≤ Submodule.span K {z | ∃ σ j, j + e σ ≤ M ∧ z = x ^ j * y σ}) ∧
      (∀ M ≤ M₁, LinearIndependent K
        (fun p : {p : Fin d' × ℕ // p.2 + e p.1 ≤ M} => x ^ p.val.2 * y p.val.1)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_exists_flagAdaptedBasisAt_lSpace_nsmul_poleDivisor.solution
