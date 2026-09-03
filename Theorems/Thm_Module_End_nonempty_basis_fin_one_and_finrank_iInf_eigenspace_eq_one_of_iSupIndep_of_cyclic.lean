import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Order.SupIndep
import P2M.Util
import P2M.Sol.S_Module_End_nonempty_basis_fin_one_and_finrank_iInf_eigenspace_eq_one_of_iSupIndep_of_cyclic

set_option autoImplicit false

theorem Module.End.nonempty_basis_fin_one_and_finrank_iInf_eigenspace_eq_one_of_iSupIndep_of_cyclic
    {K : Type*} [Field K] {W : Type*} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    {ι : Type*} [Fintype ι]
    (V : ι → Submodule K W) (hVind : iSupIndep V) (hVtop : iSup V = ⊤)
    (A : Subalgebra K (Module.End K W))
    (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hstab : ∀ a ∈ A, ∀ (i : ι), ∀ v ∈ V i, a v ∈ V i)
    (e : ι → ↥A) (he₁ : ∀ (i : ι), ∀ v ∈ V i, (e i : Module.End K W) v = v)
    (he₀ : ∀ (i j : ι), j ≠ i → ∀ v ∈ V j, (e i : Module.End K W) v = 0)
    (w : ι → W) (hw : ∀ i, w i ∈ V i)
    (hcyc : ∀ (i : ι), ∀ v ∈ V i, ∃ a : ↥A, (a : Module.End K W) (w i) = v)
    (hle : ∀ (i : ι) (χ : ↥A →ₐ[K] K),
      Module.finrank K ↥(V i ⊓ ⨅ a : ↥A, Module.End.eigenspace (a : Module.End K W) (χ a)) ≤ 1) :
    Nonempty (Module.Basis (Fin 1) ↥A W) ∧
    ∀ χ : ↥A →ₐ[K] K,
      Module.finrank K ↥(⨅ a : ↥A, Module.End.eigenspace (a : Module.End K W) (χ a)) = 1 := by p2m_exact_reverting @_root_.P2MW.S_Module_End_nonempty_basis_fin_one_and_finrank_iInf_eigenspace_eq_one_of_iSupIndep_of_cyclic.solution
