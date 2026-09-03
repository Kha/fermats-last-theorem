import Mathlib
import P2M.Util
import P2M.Sol.S_Module_span_det_submatrix_eq_of_ker_eq_span_range

set_option autoImplicit false

theorem Module.span_det_submatrix_eq_of_ker_eq_span_range
    {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
    {k l : ℕ} (π : (Fin k → R) →ₗ[R] M) (hπ : Function.Surjective π)
    (X : Matrix (Fin k) (Fin l) R) (hX : LinearMap.ker π = Submodule.span R (Set.range fun j : Fin l => fun i => X i j))
    {k' l' : ℕ} (π' : (Fin k' → R) →ₗ[R] M) (hπ' : Function.Surjective π')
    (X' : Matrix (Fin k') (Fin l') R)
    (hX' : LinearMap.ker π' = Submodule.span R (Set.range fun j : Fin l' => fun i => X' i j)) :
    Ideal.span (Set.range fun c : Fin k → Fin l => (X.submatrix id c).det) =
      Ideal.span (Set.range fun c : Fin k' → Fin l' => (X'.submatrix id c).det) := by p2m_exact_reverting @_root_.P2MW.S_Module_span_det_submatrix_eq_of_ker_eq_span_range.solution
