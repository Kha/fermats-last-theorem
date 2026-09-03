import Mathlib
import Definitions.Def_HopfAlgebra_CartierDual
import P2M.Util
import P2M.Sol.S_CartierDual_exists_bialgEquiv_monoidAlgebra_of_points

theorem CartierDual.exists_bialgEquiv_monoidAlgebra_of_points
    (R : Type*) [CommRing R] (A : Type*) [CommRing A] [Bialgebra R A]
    (Γ : Type*) [CommMonoid Γ] [Finite Γ]
    (y : Γ →* WithConv (A →ₐ[R] R))
    (hy : Function.Bijective fun (a : A) (x : Γ) => y x a) :
    ∃ ψ : A ≃ₐc[R] CartierDual R (MonoidAlgebra R Γ),
      ∀ (a : A) (x : Γ), ψ a (MonoidAlgebra.single x 1) = y x a := by p2m_exact_reverting @_root_.P2MW.S_CartierDual_exists_bialgEquiv_monoidAlgebra_of_points.solution
