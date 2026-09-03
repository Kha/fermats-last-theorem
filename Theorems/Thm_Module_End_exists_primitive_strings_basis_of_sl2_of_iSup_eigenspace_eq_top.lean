import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Analysis.Complex.Basic
import P2M.Util
import P2M.Sol.S_Module_End_exists_primitive_strings_basis_of_sl2_of_iSup_eigenspace_eq_top

set_option autoImplicit false

theorem Module.End.exists_primitive_strings_basis_of_sl2_of_iSup_eigenspace_eq_top
    (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (e f h : V →ₗ[ℂ] V)
    (hhe : h ∘ₗ e - e ∘ₗ h = (2 : ℂ) • e) (hhf : h ∘ₗ f - f ∘ₗ h = -((2 : ℂ) • f)) (hef : e ∘ₗ f - f ∘ₗ e = h)
    (hdiag : ⨆ μ : ℂ, Module.End.eigenspace h μ = ⊤) :
    ∃ (r : ℕ) (t : Fin r → V) (n : Fin r → ℕ),
      (∀ i, e (t i) = 0 ∧ h (t i) = (n i : ℂ) • t i ∧ (f ^ (n i + 1)) (t i) = 0) ∧
      (∀ i (p : ℕ), p ≤ n i →
        h ((f ^ p) (t i)) = ((n i : ℂ) - 2 * (p : ℂ)) • (f ^ p) (t i) ∧
        e ((f ^ (p + 1)) (t i)) = (((p : ℂ) + 1) * ((n i : ℂ) - (p : ℂ))) • (f ^ p) (t i)) ∧
      LinearIndependent ℂ (fun x : (Σ i : Fin r, Fin (n i + 1)) => (f ^ (x.2 : ℕ)) (t x.1)) ∧
      Submodule.span ℂ (Set.range (fun x : (Σ i : Fin r, Fin (n i + 1)) => (f ^ (x.2 : ℕ)) (t x.1))) = ⊤ := by p2m_exact_reverting @_root_.P2MW.S_Module_End_exists_primitive_strings_basis_of_sl2_of_iSup_eigenspace_eq_top.solution
