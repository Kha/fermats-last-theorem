import Mathlib
import Definitions.Def_Mathlib_Algebra_IsDirectLimit
import P2M.Util
import P2M.Sol.S_Algebra_exists_finitePresentation_tensorProduct_algEquiv_of_isDirectLimit

set_option autoImplicit false

open scoped TensorProduct

universe u v w w'

theorem Algebra.exists_finitePresentation_tensorProduct_algEquiv_of_isDirectLimit
    {ι : Type u} [Preorder ι] [Nonempty ι] [IsDirectedOrder ι]
    (G : ι → Type v) [∀ i, CommRing (G i)] (f : ∀ i j : ι, i ≤ j → G i →+* G j)
    [DirectedSystem G fun i j h => ⇑(f i j h)]
    (R : Type w) [CommRing R] [∀ i, Algebra (G i) R]
    (hR : IsDirectLimit (fun i j h => ⇑(f i j h)) fun i => ⇑(algebraMap (G i) R))
    (A : Type w') [CommRing A] [Algebra R A] [Algebra.FinitePresentation R A] :
    ∃ (i : ι) (A₀ : Type v) (_ : CommRing A₀) (_ : Algebra (G i) A₀)
      (_ : Algebra.FinitePresentation (G i) A₀), Nonempty ((R ⊗[G i] A₀) ≃ₐ[R] A) := by p2m_exact_reverting @_root_.P2MW.S_Algebra_exists_finitePresentation_tensorProduct_algEquiv_of_isDirectLimit.solution
