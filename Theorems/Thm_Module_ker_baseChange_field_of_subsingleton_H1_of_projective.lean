import Mathlib
import P2M.Util
import P2M.Sol.S_Module_ker_baseChange_field_of_subsingleton_H1_of_projective

universe u v

open TensorProduct

theorem Module.ker_baseChange_field_of_subsingleton_H1_of_projective
    (R : Type u) [CommRing R]
    {C0 C1 C2 : Type v} [AddCommGroup C0] [Module R C0] [AddCommGroup C1] [Module R C1]
    [AddCommGroup C2] [Module R C2]
    [Module.Finite R C1] [Module.Projective R C1] [Module.Finite R C2] [Module.Projective R C2]
    (d0 : C0 →ₗ[R] C1) (d1 : C1 →ₗ[R] C2) (hdd : d1 ∘ₗ d0 = 0)
    (K : Type u) [Field K] [Algebra R K]
    (hH1 : LinearMap.ker (d1.baseChange K) ≤ LinearMap.range (d0.baseChange K)) :
    LinearMap.range ((LinearMap.ker d0).subtype.baseChange K) = LinearMap.ker (d0.baseChange K) ∧
      Function.Injective ((LinearMap.ker d0).subtype.baseChange K) := by p2m_exact_reverting @_root_.P2MW.S_Module_ker_baseChange_field_of_subsingleton_H1_of_projective.solution
