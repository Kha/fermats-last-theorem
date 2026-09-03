import Mathlib
import P2M.Util
import P2M.Sol.S_Bialgebra_exists_bialgEquiv_cancelBaseChange_tmul

set_option autoImplicit false

open scoped TensorProduct

theorem Bialgebra.exists_bialgEquiv_cancelBaseChange_tmul
    (R R' S : Type*) [CommRing R] [CommRing R'] [CommRing S] [Algebra R R'] [Algebra R' S] [Algebra R S]
    [IsScalarTower R R' S] (C : Type*) [CommRing C] [Bialgebra R C] :
    ∃ e : S ⊗[R'] (R' ⊗[R] C) ≃ₐc[S] S ⊗[R] C, ∀ (s : S) (r : R') (c : C), e (s ⊗ₜ (r ⊗ₜ c)) = (r • s) ⊗ₜ c := by p2m_exact_reverting @_root_.P2MW.S_Bialgebra_exists_bialgEquiv_cancelBaseChange_tmul.solution
