import Mathlib
import P2M.Util
import P2M.Sol.S_Module_Grassmannian_exists_injective_and_bijective_of_span_eq_top

set_option autoImplicit false

open scoped TensorProduct

theorem Module.Grassmannian.exists_injective_and_bijective_of_span_eq_top
    (R : Type) [CommRing R] (M : Type) [AddCommGroup M] [Module R M] (k : ℕ)
    (ι : Type) (g : ι → M) (hg : Submodule.span R (Set.range g) = ⊤)
    (K : Type) [Field K] [Algebra R K] (N : Module.Grassmannian K (K ⊗[R] M) k) :
    ∃ I : Fin k → ι, Function.Injective I ∧
      Function.Bijective fun v : Fin k → K =>
        ∑ i, v i • N.toSubmodule.mkQ ((1 : K) ⊗ₜ[R] g (I i)) := by p2m_exact_reverting @_root_.P2MW.S_Module_Grassmannian_exists_injective_and_bijective_of_span_eq_top.solution
