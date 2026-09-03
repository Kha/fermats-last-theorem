import Mathlib
import P2M.Util
import P2M.Sol.S_MvPolynomial_exists_isHomogeneous_eq_sub_sub_of_cocycle_of_symmetric

set_option autoImplicit false

universe u v

theorem MvPolynomial.exists_isHomogeneous_eq_sub_sub_of_cocycle_of_symmetric
    {R : Type u} [CommRing R] {σ : Type v} [Finite σ] (n : ℕ) (hn : IsUnit (n : R))
    (Γ : MvPolynomial (σ ⊕ σ) R) (hhom : Γ.IsHomogeneous n)
    (hsymm : MvPolynomial.rename Sum.swap Γ = Γ)
    (hcoc :
      MvPolynomial.aeval (Sum.elim (fun s => (MvPolynomial.X (Sum.inr (Sum.inl s)) : MvPolynomial (σ ⊕ (σ ⊕ σ)) R))
          (fun s => MvPolynomial.X (Sum.inr (Sum.inr s)))) Γ
        - MvPolynomial.aeval (Sum.elim (fun s => (MvPolynomial.X (Sum.inl s) + MvPolynomial.X (Sum.inr (Sum.inl s)) :
            MvPolynomial (σ ⊕ (σ ⊕ σ)) R)) (fun s => MvPolynomial.X (Sum.inr (Sum.inr s)))) Γ
        + MvPolynomial.aeval (Sum.elim (fun s => (MvPolynomial.X (Sum.inl s) : MvPolynomial (σ ⊕ (σ ⊕ σ)) R))
            (fun s => MvPolynomial.X (Sum.inr (Sum.inl s)) + MvPolynomial.X (Sum.inr (Sum.inr s)))) Γ
        - MvPolynomial.aeval (Sum.elim (fun s => (MvPolynomial.X (Sum.inl s) : MvPolynomial (σ ⊕ (σ ⊕ σ)) R))
            (fun s => MvPolynomial.X (Sum.inr (Sum.inl s)))) Γ = 0) :
    ∃ h : MvPolynomial σ R, h.IsHomogeneous n ∧
      Γ = MvPolynomial.aeval (fun s => (MvPolynomial.X (Sum.inl s) + MvPolynomial.X (Sum.inr s) : MvPolynomial (σ ⊕ σ) R)) h
        - MvPolynomial.rename Sum.inl h - MvPolynomial.rename Sum.inr h := by p2m_exact_reverting @_root_.P2MW.S_MvPolynomial_exists_isHomogeneous_eq_sub_sub_of_cocycle_of_symmetric.solution
