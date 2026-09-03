import Mathlib
import Definitions.Def_Mathlib_Algebra_IsDirectLimit
import P2M.Util
import P2M.Sol.S_Algebra_exists_isDirectLimit_of_finitePresentation

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem Algebra.exists_isDirectLimit_of_finitePresentation
    (R : Type u) [CommRing R] (A : Type u) [CommRing A] [Algebra R A] :
    ∃ (ι : Type u) (_ : Preorder ι) (_ : Nonempty ι) (_ : IsDirected ι (· ≤ ·))
      (S : ι → Type u) (_ : ∀ i, CommRing (S i)) (_ : ∀ i, Algebra R (S i))
      (_ : ∀ i, Algebra.FinitePresentation R (S i))
      (t : ∀ i j : ι, i ≤ j → (S i →ₐ[R] S j)) (c : ∀ i, S i →ₐ[R] A)
      (_ : DirectedSystem S fun i j h => ⇑(t i j h)),
      IsDirectLimit (fun i j h => ⇑(t i j h)) fun i => ⇑(c i) := by p2m_exact_reverting @_root_.P2MW.S_Algebra_exists_isDirectLimit_of_finitePresentation.solution
