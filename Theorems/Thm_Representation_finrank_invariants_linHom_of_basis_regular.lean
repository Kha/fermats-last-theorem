import Mathlib
import P2M.Util
import P2M.Sol.S_Representation_finrank_invariants_linHom_of_basis_regular

set_option autoImplicit false
universe u
open Module
theorem Representation.finrank_invariants_linHom_of_basis_regular
    {k : Type*} [Field k] {Δ : Type*} [Group Δ] [Fintype Δ]
    {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V] (N : Representation k Δ V)
    {VR : Type*} [AddCommGroup VR] [Module k VR] (R : Representation k Δ VR)
    {ι : Type*} [Fintype ι] (b : Module.Basis (Δ × ι) k VR)
    (hb : ∀ (d e : Δ) (i : ι), R d (b (e, i)) = b (d * e, i)) :
    finrank k (N.linHom R).invariants = Fintype.card ι * finrank k V := by p2m_exact_reverting @_root_.P2MW.S_Representation_finrank_invariants_linHom_of_basis_regular.solution
