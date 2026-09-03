import Mathlib
import Definitions.Def_GroupCohomology_TransferHecke
import P2M.Util
import P2M.Sol.S_HeckeCohomology_exists_eigenvector_H1_or_forall_eq_of_eigenvector_H1_of_shortExact

set_option autoImplicit false

theorem HeckeCohomology.exists_eigenvector_H1_or_forall_eq_of_eigenvector_H1_of_shortExact
    {κ Γ : Type} [Field κ] [Group Γ]
    {X : CategoryTheory.ShortComplex (Rep κ Γ)} (hX : X.ShortExact)
    {ι : Type} (S₁ S₂ : ι → Subgroup Γ) (c : ∀ i, ↥(S₂ i) →* ↥(S₁ i)) [∀ i, (S₂ i).FiniteIndex]
    (φ₁ : ∀ i, X.X₁ →ₗ[κ] X.X₁) (hφ₁ : ∀ i, HeckeCohomology.IsTwist (S₁ i) (S₂ i) (c i) X.X₁ (φ₁ i))
    (φ₂ : ∀ i, X.X₂ →ₗ[κ] X.X₂) (hφ₂ : ∀ i, HeckeCohomology.IsTwist (S₁ i) (S₂ i) (c i) X.X₂ (φ₂ i))
    (φ₃ : ∀ i, X.X₃ →ₗ[κ] X.X₃) (hφ₃ : ∀ i, HeckeCohomology.IsTwist (S₁ i) (S₂ i) (c i) X.X₃ (φ₃ i))
    (hf : ∀ (i : ι) (a : X.X₁), X.f.hom (φ₁ i a) = φ₂ i (X.f.hom a))
    (hg : ∀ (i : ι) (b : X.X₂), X.g.hom (φ₂ i b) = φ₃ i (X.g.hom b))
    (cc : ι → κ)
    (hinv : ∀ (i : ι) (z : X.X₃.ρ.invariants),
      HeckeCohomology.heckeInv (S₁ i) (S₂ i) (c i) X.X₃ (φ₃ i) (hφ₃ i) z = cc i • z)
    (lam : ι → κ)
    (hocc : ∃ x : groupCohomology.H1 X.X₁, x ≠ 0 ∧
      ∀ i : ι, HeckeCohomology.heckeH1 (S₁ i) (S₂ i) (c i) X.X₁ (φ₁ i) (hφ₁ i) x = lam i • x) :
    (∃ y : groupCohomology.H1 X.X₂, y ≠ 0 ∧
      ∀ i : ι, HeckeCohomology.heckeH1 (S₁ i) (S₂ i) (c i) X.X₂ (φ₂ i) (hφ₂ i) y = lam i • y) ∨
    ∀ i : ι, lam i = cc i := by p2m_exact_reverting @_root_.P2MW.S_HeckeCohomology_exists_eigenvector_H1_or_forall_eq_of_eigenvector_H1_of_shortExact.solution
