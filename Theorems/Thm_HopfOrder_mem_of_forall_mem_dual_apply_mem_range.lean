import Mathlib
import Definitions.Def_HopfAlgebra_CartierDual
import P2M.Util
import P2M.Sol.S_HopfOrder_mem_of_forall_mem_dual_apply_mem_range
attribute [-simp] HopfOrder.doubleCmp_tmul HopfOrder.tensorSqHom_tmul HopfOrder.baseChangeHom_tmul

set_option autoImplicit false

open scoped TensorProduct

theorem HopfOrder.mem_of_forall_mem_dual_apply_mem_range
    {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    {A : Type*} [CommRing A] [HopfAlgebra K A] [Algebra R A] [IsScalarTower R K A]
    [Module.Finite K A] [Coalgebra.IsCocomm K A]
    [Algebra R (CartierDual K A)] [IsScalarTower R K (CartierDual K A)]
    (S : Subalgebra R A)
    (hfin : Module.Finite R ↥S) (hspan : Submodule.span K (S : Set A) = ⊤)
    (S' : Subalgebra R (CartierDual K A))
    (hS' : ∀ φ : CartierDual K A, φ ∈ S' ↔ ∀ b ∈ S, φ b ∈ (algebraMap R K).range)
    (a : A) (ha : ∀ φ ∈ S', φ a ∈ (algebraMap R K).range) : a ∈ S := by p2m_exact_reverting @_root_.P2MW.S_HopfOrder_mem_of_forall_mem_dual_apply_mem_range.solution
