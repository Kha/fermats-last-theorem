import Mathlib
import P2M.Util
import P2M.Sol.S_Module_free_quotient_range_of_ker_baseChange_residueField_le

set_option autoImplicit false

universe u v w

open scoped TensorProduct

theorem Module.free_quotient_range_of_ker_baseChange_residueField_le
    {R : Type u} [CommRing R] [IsLocalRing R]
    {M : Type v} {N : Type w} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.Finite R M] [Module.Finite R N] [Module.Free R N] (f : M →ₗ[R] N)
    (h : LinearMap.ker (f.baseChange (IsLocalRing.ResidueField R)) ≤
      LinearMap.range ((LinearMap.ker f).subtype.baseChange (IsLocalRing.ResidueField R))) :
    Module.Free R (N ⧸ LinearMap.range f) := by p2m_exact_reverting @_root_.P2MW.S_Module_free_quotient_range_of_ker_baseChange_residueField_le.solution
