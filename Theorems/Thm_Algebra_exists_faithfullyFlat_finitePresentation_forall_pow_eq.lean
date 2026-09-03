import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_exists_faithfullyFlat_finitePresentation_forall_pow_eq

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem Algebra.exists_faithfullyFlat_finitePresentation_forall_pow_eq
    {R : Type u} [CommRing R] (m : ℕ) (hm : 0 < m) {ι : Type} [Finite ι] (u : ι → Rˣ) :
    ∃ (R' : Type u) (_ : CommRing R') (_ : Algebra R R'),
      Module.FaithfullyFlat R R' ∧ Algebra.FinitePresentation R R' ∧
      ∃ v : ι → R'ˣ, ∀ i, (v i : R') ^ m = algebraMap R R' (u i) := by p2m_exact_reverting @_root_.P2MW.S_Algebra_exists_faithfullyFlat_finitePresentation_forall_pow_eq.solution
