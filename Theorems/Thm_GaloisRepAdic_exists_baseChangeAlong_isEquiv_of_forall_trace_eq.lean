import Mathlib
import Definitions.Def_GaloisRep_Adic
import P2M.Util
import P2M.Sol.S_GaloisRepAdic_exists_baseChangeAlong_isEquiv_of_forall_trace_eq

set_option autoImplicit false

open IsLocalRing

theorem GaloisRepAdic.exists_baseChangeAlong_isEquiv_of_forall_trace_eq
    {T : Type} [CommRing T] [IsLocalRing T] [IsNoetherianRing T]
    [IsAdicComplete (maximalIdeal T) T] [Finite (ResidueField T)]
    {n : ℕ} (A : Fin n → Type) [∀ i, CommRing (A i)] [∀ i, IsLocalRing (A i)]
    [∀ i, Algebra T (A i)] [∀ i, Module.Finite T (A i)]
    [hloc : ∀ i, IsLocalHom (algebraMap T (A i))]
    (hinj : ∀ x : T, (∀ i, algebraMap T (A i) x = 0) → x = 0)
    (ρbar : ResidualGaloisRep (ResidueField T)) (habs : ρbar.IsAbsolutelyIrreducible)
    (ρ : ∀ i, GaloisRepAdic (A i))
    (hres : ∀ i, (ρ i).residual.IsEquiv
      (ρbar.baseChangeAlong (ResidueField.map (algebraMap T (A i)))))
    (τ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → T)
    (htr : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (i : Fin n),
      (ρ i).trace σ = algebraMap T (A i) (τ σ)) :
    ∃ ρ' : GaloisRepAdic T,
      ∀ i, ((ρ'.baseChangeAlong (algebraMap T (A i)) (hloc i)).IsEquiv (ρ i)) := by p2m_exact_reverting @_root_.P2MW.S_GaloisRepAdic_exists_baseChangeAlong_isEquiv_of_forall_trace_eq.solution
