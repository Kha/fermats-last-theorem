import Mathlib
import Definitions.Def_HopfAlgebra_CartierDual
import P2M.Util
import P2M.Sol.S_CartierDual_exists_bialgEquiv_bidual

theorem CartierDual.exists_bialgEquiv_bidual
    (R : Type*) [CommRing R] (A : Type*) [CommRing A] [Bialgebra R A]
    [Module.Finite R A] [Module.Free R A] [Coalgebra.IsCocomm R A] :
    ∃ e : A ≃ₐc[R] CartierDual R (CartierDual R A), ∀ (a : A) (φ : CartierDual R A), e a φ = φ a := by p2m_exact_reverting @_root_.P2MW.S_CartierDual_exists_bialgEquiv_bidual.solution
