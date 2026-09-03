import Mathlib
import P2M.Util
import P2M.Sol.S_AddCommGroup_exists_fg_saturation_of_isHomogeneous_degree

set_option autoImplicit false

theorem AddCommGroup.exists_fg_saturation_of_isHomogeneous_degree
    {R : Type*} [AddCommGroup R] (deg : R → ℤ) (D : ℕ) (hD : D ≠ 0)
    (hpoly : ∀ (m : ℕ) (α : Fin m → R), ∃ P : MvPolynomial (Fin m) ℚ, P.IsHomogeneous D ∧
      ∀ n : Fin m → ℤ, (deg (∑ i, n i • α i) : ℚ) = MvPolynomial.eval (fun i => (n i : ℚ)) P)
    (hsep : ∀ x : R, x ≠ 0 → deg x ≠ 0)
    (M : AddSubgroup R) (hM : M.FG) :
    ∃ M' : AddSubgroup R, M'.FG ∧ ∀ x : R, x ∈ M' ↔ ∃ k : ℤ, k ≠ 0 ∧ k • x ∈ M := by p2m_exact_reverting @_root_.P2MW.S_AddCommGroup_exists_fg_saturation_of_isHomogeneous_degree.solution
