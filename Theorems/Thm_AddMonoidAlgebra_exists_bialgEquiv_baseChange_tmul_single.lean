import Mathlib
import P2M.Util
import P2M.Sol.S_AddMonoidAlgebra_exists_bialgEquiv_baseChange_tmul_single

set_option autoImplicit false

open scoped TensorProduct

theorem AddMonoidAlgebra.exists_bialgEquiv_baseChange_tmul_single
    (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] (G : Type*) [AddCommMonoid G] :
    ∃ e : S ⊗[R] AddMonoidAlgebra R G ≃ₐc[S] AddMonoidAlgebra S G,
      ∀ (s : S) (g : G) (r : R), e (s ⊗ₜ AddMonoidAlgebra.single g r) = AddMonoidAlgebra.single g (r • s) := by p2m_exact_reverting @_root_.P2MW.S_AddMonoidAlgebra_exists_bialgEquiv_baseChange_tmul_single.solution
