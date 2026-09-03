import Mathlib
import Definitions.Def_Mathlib_Algebra_IsDirectLimit
import P2M.Util
import P2M.Sol.S_Algebra_FinitePresentation_of_forall_isDirectLimit_exists_comp_eq

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem Algebra.FinitePresentation.of_forall_isDirectLimit_exists_comp_eq
    {R : Type u} [CommRing R] {A : Type u} [CommRing A] [Algebra R A]
    (H : ∀ (ι : Type u) [Preorder ι] [Nonempty ι] [IsDirected ι (· ≤ ·)]
      (S : ι → Type u) [∀ i, CommRing (S i)] [∀ i, Algebra R (S i)]
      (t : ∀ i j : ι, i ≤ j → (S i →ₐ[R] S j)) [DirectedSystem S fun i j h => ⇑(t i j h)]
      (L : Type u) [CommRing L] [Algebra R L] (c : ∀ i, S i →ₐ[R] L)
      [IsDirectLimit (fun i j h => ⇑(t i j h)) fun i => ⇑(c i)]
      (ψ : A →ₐ[R] L), ∃ (i : ι) (φ : A →ₐ[R] S i), (c i).comp φ = ψ) :
    Algebra.FinitePresentation R A := by p2m_exact_reverting @_root_.P2MW.S_Algebra_FinitePresentation_of_forall_isDirectLimit_exists_comp_eq.solution
