import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.RingTheory.Ideal.Operations
import P2M.Util
import P2M.Sol.S_Module_Basis_repr_apply_mem_of_mem_ideal_smul_top

theorem Module.Basis.repr_apply_mem_of_mem_ideal_smul_top {R : Type*} [CommRing R] {N : Type*} [AddCommGroup N] [Module R N] {κ : Type*} (b : Module.Basis κ R N) (I : Ideal R) {x : N} (hx : x ∈ (I • ⊤ : Submodule R N)) (k : κ) :
    b.repr x k ∈ I := by p2m_exact_reverting @_root_.P2MW.S_Module_Basis_repr_apply_mem_of_mem_ideal_smul_top.solution
