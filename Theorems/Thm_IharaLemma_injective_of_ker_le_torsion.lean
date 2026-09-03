import Mathlib.Algebra.Module.LocalizedModule.Basic
import P2M.Util
import P2M.Sol.S_IharaLemma_injective_of_ker_le_torsion

set_option autoImplicit false

theorem IharaLemma.injective_of_ker_le_torsion {R : Type*} [CommRing R] (S : Submonoid R)
    {V W V' W' : Type*} [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
    [AddCommGroup V'] [Module R V'] [AddCommGroup W'] [Module R W']
    (g : V →ₗ[R] V') [IsLocalizedModule S g] (h : W →ₗ[R] W') [IsLocalizedModule S h]
    (f : V →ₗ[R] W) (F : V' →ₗ[R] W') (hcomm : ∀ v, F (g v) = h (f v))
    (E : Submodule R V) (hE : ∀ e ∈ E, ∃ s : S, (s : R) • e = 0) (hker : ∀ v, f v = 0 → v ∈ E) :
    Function.Injective F := by p2m_exact_reverting @_root_.P2MW.S_IharaLemma_injective_of_ker_le_torsion.solution
