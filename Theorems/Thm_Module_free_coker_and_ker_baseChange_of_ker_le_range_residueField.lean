import Mathlib
import P2M.Util
import P2M.Sol.S_Module_free_coker_and_ker_baseChange_of_ker_le_range_residueField

universe u v

open TensorProduct

theorem Module.free_coker_and_ker_baseChange_of_ker_le_range_residueField
    (R : Type u) [CommRing R] [IsLocalRing R]
    {C0 C1 C2 : Type v} [AddCommGroup C0] [Module R C0] [AddCommGroup C1] [Module R C1]
    [AddCommGroup C2] [Module R C2] [Module.Finite R C1] [Module.Free R C1] [Module.Finite R C2] [Module.Free R C2]
    (d0 : C0 →ₗ[R] C1) (d1 : C1 →ₗ[R] C2) (hdd : d1 ∘ₗ d0 = 0)
    (hH1 : LinearMap.ker (d1.baseChange (IsLocalRing.ResidueField R)) ≤
      LinearMap.range (d0.baseChange (IsLocalRing.ResidueField R))) :
    Module.Free R (C1 ⧸ LinearMap.range d0) ∧
      ∀ (A : Type u) [CommRing A] [Algebra R A],
        LinearMap.range ((LinearMap.ker d0).subtype.baseChange A) = LinearMap.ker (d0.baseChange A) ∧
          Function.Injective ((LinearMap.ker d0).subtype.baseChange A) := by p2m_exact_reverting @_root_.P2MW.S_Module_free_coker_and_ker_baseChange_of_ker_le_range_residueField.solution
