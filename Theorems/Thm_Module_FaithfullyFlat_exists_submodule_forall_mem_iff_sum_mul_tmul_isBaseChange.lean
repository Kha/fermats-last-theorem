import Mathlib
import Definitions.Def_Algebra_DescentCofaces
import P2M.Util
import P2M.Sol.S_Module_FaithfullyFlat_exists_submodule_forall_mem_iff_sum_mul_tmul_isBaseChange

set_option autoImplicit false

open Algebra.DescentCofaces
open scoped TensorProduct

universe u v

theorem Module.FaithfullyFlat.exists_submodule_forall_mem_iff_sum_mul_tmul_isBaseChange
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A] [Module.FaithfullyFlat R A]
    {G : Type v} [AddCommGroup G] [Fintype G]
    (e : G → A ⊗[R] A) (he : CompleteOrthogonalIdempotents e)
    (hcoc : ∀ k, ∑ i, (c₁₂ R A).hom (e i) * (c₂₃ R A).hom (e (k - i)) = (c₁₃ R A).hom (e k)) :
    ∃ M : Submodule R (G → A),
      (∀ f : G → A, f ∈ M ↔ ∀ k, ∑ m, e m * (f (k - m) ⊗ₜ[R] 1) = 1 ⊗ₜ[R] f k) ∧
      IsBaseChange A M.subtype := by p2m_exact_reverting @_root_.P2MW.S_Module_FaithfullyFlat_exists_submodule_forall_mem_iff_sum_mul_tmul_isBaseChange.solution
