import Mathlib
import P2M.Util
import P2M.Sol.S_Module_Grassmannian_exists_isOpen_forall_bijective_map_iff_range_comap_subset

set_option autoImplicit false

open scoped TensorProduct

theorem Module.Grassmannian.exists_isOpen_forall_bijective_map_iff_range_comap_subset
    (R : Type) [CommRing R] (M : Type) [AddCommGroup M] [Module R M] (k : ℕ) (x : Fin k → M)
    (A : Type) [CommRing A] [Algebra R A] (N : Module.Grassmannian A (A ⊗[R] M) k) :
    ∃ U : Set (PrimeSpectrum A), IsOpen U ∧
      ∀ (B : Type) [CommRing B] [Algebra R B] (φ : A →ₐ[R] B),
        (Function.Bijective fun v : Fin k → B =>
            ∑ i, v i • (Module.Grassmannian.map φ N).toSubmodule.mkQ ((1 : B) ⊗ₜ[R] x i)) ↔
          Set.range (PrimeSpectrum.comap φ.toRingHom) ⊆ U := by p2m_exact_reverting @_root_.P2MW.S_Module_Grassmannian_exists_isOpen_forall_bijective_map_iff_range_comap_subset.solution
