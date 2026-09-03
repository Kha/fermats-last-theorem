import Mathlib
import Definitions.Def_AlgebraicGeometry_DoubleComplex
import P2M.Util
import P2M.Sol.S_DoubleComplex_exists_HTot_transpose_equiv_mk_eq_mk_swap

set_option autoImplicit false

universe u

theorem DoubleComplex.exists_HTot_transpose_equiv_mk_eq_mk_swap
    {R : Type u} [CommRing R] (D : DoubleComplex.Bounded R) (n : ℕ) :
    ∃ e : DoubleComplex.HTot (DoubleComplex.transpose D) n ≃ₗ[R] DoubleComplex.HTot D n,
      ∀ (z : DoubleComplex.Tot (DoubleComplex.transpose D) n)
        (hz : z ∈ LinearMap.ker (DoubleComplex.dTot (DoubleComplex.transpose D) n)),
        ∃ hSz : (fun pq : DoubleComplex.Diag n =>
            ((-1 : ℤ) ^ (pq.1.1 * pq.1.2)) • (show D.C pq.1.1 pq.1.2 from z ⟨(pq.1.2, pq.1.1), by have := pq.2; omega⟩))
              ∈ LinearMap.ker (DoubleComplex.dTot D n),
          e (Submodule.Quotient.mk ⟨z, hz⟩) = Submodule.Quotient.mk ⟨_, hSz⟩ := by p2m_exact_reverting @_root_.P2MW.S_DoubleComplex_exists_HTot_transpose_equiv_mk_eq_mk_swap.solution
