import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_TensorProduct_specialFibre_coordinates_sumElim_tmul

open scoped TensorProduct

universe u v w w'

theorem Algebra.TensorProduct.specialFibre_coordinates_sumElim_tmul
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] [Algebra 𝓞 (ZMod p)]
    (R : ℕ → Type v) [∀ v, CommRing (R v)] [∀ v, Algebra 𝓞 (R v)]
    (t : ∀ v, R (v + 1) →ₐ[𝓞] R v)
    {σ : Type w} [Finite σ] (x : ∀ v, σ → R v) (hxt : ∀ v i, t v (x (v + 1) i) = x v i)
    (hxrad : ∀ v i, x v i ∈ (Ideal.span {(p : R v)}).radical)
    (hxsurj : ∀ v, Function.Surjective
      (MvPolynomial.aeval (fun i => (1 : ZMod p) ⊗ₜ[𝓞] x v i) :
        MvPolynomial σ (ZMod p) →ₐ[ZMod p] TensorProduct 𝓞 (ZMod p) (R v)))
    (hxker : ∀ N : ℕ, ∃ v, RingHom.ker
      (MvPolynomial.aeval (fun i => (1 : ZMod p) ⊗ₜ[𝓞] x v i) :
        MvPolynomial σ (ZMod p) →ₐ[ZMod p] TensorProduct 𝓞 (ZMod p) (R v)) ≤
      (Ideal.span (Set.range (MvPolynomial.X : σ → MvPolynomial σ (ZMod p)))) ^ N)
    (R' : ℕ → Type v) [∀ v, CommRing (R' v)] [∀ v, Algebra 𝓞 (R' v)]
    (t' : ∀ v, R' (v + 1) →ₐ[𝓞] R' v)
    {σ' : Type w'} [Finite σ'] (x' : ∀ v, σ' → R' v) (hxt' : ∀ v i, t' v (x' (v + 1) i) = x' v i)
    (hxrad' : ∀ v i, x' v i ∈ (Ideal.span {(p : R' v)}).radical)
    (hxsurj' : ∀ v, Function.Surjective
      (MvPolynomial.aeval (fun i => (1 : ZMod p) ⊗ₜ[𝓞] x' v i) :
        MvPolynomial σ' (ZMod p) →ₐ[ZMod p] TensorProduct 𝓞 (ZMod p) (R' v)))
    (hxker' : ∀ N : ℕ, ∃ v, RingHom.ker
      (MvPolynomial.aeval (fun i => (1 : ZMod p) ⊗ₜ[𝓞] x' v i) :
        MvPolynomial σ' (ZMod p) →ₐ[ZMod p] TensorProduct 𝓞 (ZMod p) (R' v)) ≤
      (Ideal.span (Set.range (MvPolynomial.X : σ' → MvPolynomial σ' (ZMod p)))) ^ N) :
    (∀ v s, Algebra.TensorProduct.map (t v) (t' v)
        (Sum.elim (fun i => x (v + 1) i ⊗ₜ[𝓞] (1 : R' (v + 1)))
          (fun i => (1 : R (v + 1)) ⊗ₜ[𝓞] x' (v + 1) i) s) =
      Sum.elim (fun i => x v i ⊗ₜ[𝓞] (1 : R' v)) (fun i => (1 : R v) ⊗ₜ[𝓞] x' v i) s) ∧
    (∀ v s, Sum.elim (fun i => x v i ⊗ₜ[𝓞] (1 : R' v)) (fun i => (1 : R v) ⊗ₜ[𝓞] x' v i) s ∈
      (Ideal.span {(p : R v ⊗[𝓞] R' v)}).radical) ∧
    (∀ v, Function.Surjective
      (MvPolynomial.aeval (fun s => (1 : ZMod p) ⊗ₜ[𝓞]
          Sum.elim (fun i => x v i ⊗ₜ[𝓞] (1 : R' v)) (fun i => (1 : R v) ⊗ₜ[𝓞] x' v i) s) :
        MvPolynomial (σ ⊕ σ') (ZMod p) →ₐ[ZMod p] TensorProduct 𝓞 (ZMod p) (R v ⊗[𝓞] R' v))) ∧
    (∀ N : ℕ, ∃ v, RingHom.ker
      (MvPolynomial.aeval (fun s => (1 : ZMod p) ⊗ₜ[𝓞]
          Sum.elim (fun i => x v i ⊗ₜ[𝓞] (1 : R' v)) (fun i => (1 : R v) ⊗ₜ[𝓞] x' v i) s) :
        MvPolynomial (σ ⊕ σ') (ZMod p) →ₐ[ZMod p] TensorProduct 𝓞 (ZMod p) (R v ⊗[𝓞] R' v)) ≤
      (Ideal.span (Set.range
        (MvPolynomial.X : σ ⊕ σ' → MvPolynomial (σ ⊕ σ') (ZMod p)))) ^ N) := by p2m_exact_reverting @_root_.P2MW.S_Algebra_TensorProduct_specialFibre_coordinates_sumElim_tmul.solution
