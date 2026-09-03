import Mathlib
import P2M.Util
import P2M.Sol.S_PadicAlgCl_exists_forall_ringHom_apply_algebraMap_eq_of_free_of_ker_eq_span_pow

set_option autoImplicit false

theorem PadicAlgCl.exists_forall_ringHom_apply_algebraMap_eq_of_free_of_ker_eq_span_pow
    (p : ℕ) [Fact p.Prime]
    (B : ℕ → Type) [∀ i, CommRing (B i)]
    [∀ i, Algebra (integralClosure ℤ_[p] (PadicAlgCl p) ⧸ Ideal.span {(p : integralClosure ℤ_[p] (PadicAlgCl p)) ^ i}) (B i)]
    [∀ i, Module.Finite (integralClosure ℤ_[p] (PadicAlgCl p) ⧸ Ideal.span {(p : integralClosure ℤ_[p] (PadicAlgCl p)) ^ i}) (B i)]
    [∀ i, Module.Free (integralClosure ℤ_[p] (PadicAlgCl p) ⧸ Ideal.span {(p : integralClosure ℤ_[p] (PadicAlgCl p)) ^ i}) (B i)]
    (ρ : ∀ i, B (i + 1) →+* B i)
    (hρ : ∀ (i : ℕ) (x : integralClosure ℤ_[p] (PadicAlgCl p)),
      ρ i (algebraMap (integralClosure ℤ_[p] (PadicAlgCl p) ⧸ Ideal.span {(p : integralClosure ℤ_[p] (PadicAlgCl p)) ^ (i + 1)}) (B (i + 1))
        (Ideal.Quotient.mk _ x)) =
        algebraMap (integralClosure ℤ_[p] (PadicAlgCl p) ⧸ Ideal.span {(p : integralClosure ℤ_[p] (PadicAlgCl p)) ^ i}) (B i) (Ideal.Quotient.mk _ x))
    (hρs : ∀ i, Function.Surjective (ρ i))
    (hker : ∀ i, RingHom.ker (ρ i) =
      Ideal.span {algebraMap (integralClosure ℤ_[p] (PadicAlgCl p) ⧸ Ideal.span {(p : integralClosure ℤ_[p] (PadicAlgCl p)) ^ (i + 1)}) (B (i + 1))
        (Ideal.Quotient.mk _ ((p : integralClosure ℤ_[p] (PadicAlgCl p)) ^ i))})
    (ψ : B 1 →+* integralClosure ℤ_[p] (PadicAlgCl p) ⧸ (Ideal.span {(p : integralClosure ℤ_[p] (PadicAlgCl p))}).radical)
    (hψ : ∀ x : integralClosure ℤ_[p] (PadicAlgCl p),
      ψ (algebraMap (integralClosure ℤ_[p] (PadicAlgCl p) ⧸ Ideal.span {(p : integralClosure ℤ_[p] (PadicAlgCl p)) ^ 1}) (B 1) (Ideal.Quotient.mk _ x)) =
        Ideal.Quotient.mk _ x) :
    ∃ σ : ∀ i, B i →+* integralClosure ℤ_[p] (PadicAlgCl p) ⧸ Ideal.span {(p : integralClosure ℤ_[p] (PadicAlgCl p)) ^ i},
      (∀ (i : ℕ) (x : integralClosure ℤ_[p] (PadicAlgCl p) ⧸ Ideal.span {(p : integralClosure ℤ_[p] (PadicAlgCl p)) ^ i}),
        σ i (algebraMap (integralClosure ℤ_[p] (PadicAlgCl p) ⧸ Ideal.span {(p : integralClosure ℤ_[p] (PadicAlgCl p)) ^ i}) (B i) x) = x) ∧
      (∀ (i : ℕ) (b : B (i + 1)) (x : integralClosure ℤ_[p] (PadicAlgCl p)),
        σ (i + 1) b = Ideal.Quotient.mk _ x → σ i (ρ i b) = Ideal.Quotient.mk _ x) ∧
      ∀ b : B 1, ψ b = 0 → IsNilpotent (σ 1 b) := by p2m_exact_reverting @_root_.P2MW.S_PadicAlgCl_exists_forall_ringHom_apply_algebraMap_eq_of_free_of_ker_eq_span_pow.solution
