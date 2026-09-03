import Mathlib
import Definitions.Def_AlgebraicCurve_AdelicIndex
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_ell_nsmul_eq_card_of_flagAdaptedBasisAt

open AlgebraicCurve

theorem AlgebraicCurve.ell_nsmul_eq_card_of_flagAdaptedBasisAt
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (x : F) (D : Divisor K F) (hD : ∀ v : Place K F, D v = max 0 (-v.ord x))
    {d' : ℕ} (y : Fin d' → F) (e : Fin d' → ℕ)
    (hyL : ∀ σ, y σ ∈ LSpace ((e σ) • D))
    (m : ℕ) [FiniteDimensional K ↥(LSpace (m • D))]
    (hspan : (LSpace (m • D) : Submodule K F)
      ≤ Submodule.span K {z | ∃ σ j, j + e σ ≤ m ∧ z = x ^ j * y σ})
    (hLI : LinearIndependent K
      (fun p : {p : Fin d' × ℕ // p.2 + e p.1 ≤ m} => x ^ p.val.2 * y p.val.1)) :
    ell (m • D)
      = ∑ σ ∈ (Finset.univ : Finset (Fin d')).filter (fun σ => e σ ≤ m), (m + 1 - e σ) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_ell_nsmul_eq_card_of_flagAdaptedBasisAt.solution
