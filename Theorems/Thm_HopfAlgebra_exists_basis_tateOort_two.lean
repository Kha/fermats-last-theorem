import Mathlib
import P2M.Util
import P2M.Sol.S_HopfAlgebra_exists_basis_tateOort_two

universe u v
theorem HopfAlgebra.exists_basis_tateOort_two {R : Type u} [CommRing R] {H : Type v} [CommRing H] [HopfAlgebra R H]
    [Module.Finite R H] [Module.Free R H] (hrank : Module.finrank R H = 2) :
    ∃ (e : Module.Basis (Fin 2) R H) (a b : R),
      e 0 = 1 ∧ a * b = 2 ∧ Coalgebra.counit (R := R) (e 1) = 0 ∧ e 1 * e 1 = a • e 1 ∧
      Coalgebra.comul (R := R) (e 1) = e 1 ⊗ₜ[R] 1 + 1 ⊗ₜ[R] e 1 - b • (e 1 ⊗ₜ[R] e 1) ∧
      HopfAlgebra.antipode R (e 1) = e 1 := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_exists_basis_tateOort_two.solution
