import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.Algebra.Algebra.Hom
import P2M.Util
import P2M.Sol.S_Module_exists_ne_zero_forall_smul_eq_smul_of_algHom

theorem Module.exists_ne_zero_forall_smul_eq_smul_of_algHom {K A V : Type*} [Field K] [CommRing A] [Algebra K A] [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower K A V] [Module.Finite K V] [FaithfulSMul A V] (χ : A →ₐ[K] K) : ∃ v : V, v ≠ 0 ∧ ∀ a : A, a • v = χ a • v := by p2m_exact_reverting @_root_.P2MW.S_Module_exists_ne_zero_forall_smul_eq_smul_of_algHom.solution
