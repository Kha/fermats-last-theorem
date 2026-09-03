import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_AdmissibleAlgebra_isAdicComplete_fixedPoints_and_exists_ringEquiv_quotient_of_ringEquiv_tensorProduct_quotient

set_option autoImplicit false

open TensorProduct

theorem AlgebraicGeometry.AdmissibleAlgebra.isAdicComplete_fixedPoints_and_exists_ringEquiv_quotient_of_ringEquiv_tensorProduct_quotient
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
    (π : 𝒪) (hπ : Irreducible π) (hcomplete : IsAdicComplete (Ideal.span {π}) 𝒪)
    (R : Type) [CommRing R] [Algebra 𝒪 R]
    (hRc : IsAdicComplete (Ideal.span {algebraMap 𝒪 R π}) R)
    (hRtf : ∀ x : R, algebraMap 𝒪 R π * x = 0 → x = 0)
    (hRft : Algebra.FiniteType 𝒪 (R ⧸ Ideal.span {algebraMap 𝒪 R π}))
    (G : Type) [Group G] [Finite G] [MulSemiringAction G R] [SMulCommClass G 𝒪 R]

    (S : Type) [CommRing S] [Algebra 𝒪 S]
    (A' : Type) [CommRing A'] [Algebra ↥(FixedPoints.subalgebra 𝒪 R G) A'] [Module.Flat ↥(FixedPoints.subalgebra 𝒪 R G) A']
    (σ : S →+* A')
    (hσ : ∀ o : 𝒪, σ (algebraMap 𝒪 S o) =
      algebraMap ↥(FixedPoints.subalgebra 𝒪 R G) A' (algebraMap 𝒪 ↥(FixedPoints.subalgebra 𝒪 R G) o))

    (R' : Type) [CommRing R'] [Algebra S R'] [MulSemiringAction G R'] [SMulCommClass G S R']
    (hR'c : IsAdicComplete (Ideal.span {algebraMap S R' (algebraMap 𝒪 S π)}) R')
    (hR'tf : ∀ x : R', algebraMap S R' (algebraMap 𝒪 S π) * x = 0 → x = 0)
    (τ : ∀ n : ℕ, ((R ⊗[↥(FixedPoints.subalgebra 𝒪 R G)] A') ⧸
        Ideal.span {(algebraMap 𝒪 R π ^ (n + 1)) ⊗ₜ[↥(FixedPoints.subalgebra 𝒪 R G)] (1 : A')}) ≃+*
      (R' ⧸ Ideal.span {algebraMap S R' (algebraMap 𝒪 S π) ^ (n + 1)}))
    (hτ_succ : ∀ (n : ℕ) (z : R ⊗[↥(FixedPoints.subalgebra 𝒪 R G)] A') (y : R'),
      τ (n + 1) (Ideal.Quotient.mk _ z) = Ideal.Quotient.mk _ y → τ n (Ideal.Quotient.mk _ z) = Ideal.Quotient.mk _ y)
    (hτ_smul : ∀ (n : ℕ) (g : G) (x : R) (w : A') (y : R'),
      τ n (Ideal.Quotient.mk _ (x ⊗ₜ[↥(FixedPoints.subalgebra 𝒪 R G)] w)) = Ideal.Quotient.mk _ y →
      τ n (Ideal.Quotient.mk _ ((g • x) ⊗ₜ[↥(FixedPoints.subalgebra 𝒪 R G)] w)) = Ideal.Quotient.mk _ (g • y))
    (hτ_σ : ∀ (n : ℕ) (s : S),
      τ n (Ideal.Quotient.mk _ ((1 : R) ⊗ₜ[↥(FixedPoints.subalgebra 𝒪 R G)] σ s)) = Ideal.Quotient.mk _ (algebraMap S R' s)) :
    IsAdicComplete (Ideal.span {algebraMap S ↥(FixedPoints.subalgebra S R' G) (algebraMap 𝒪 S π)}) ↥(FixedPoints.subalgebra S R' G) ∧
    ∃ α : ∀ n : ℕ, (A' ⧸ Ideal.span {σ (algebraMap 𝒪 S π) ^ (n + 1)}) ≃+*
        (↥(FixedPoints.subalgebra S R' G) ⧸ Ideal.span {algebraMap S ↥(FixedPoints.subalgebra S R' G) (algebraMap 𝒪 S π) ^ (n + 1)}),
      (∀ (n : ℕ) (w : A') (x : ↥(FixedPoints.subalgebra S R' G)),
        α (n + 1) (Ideal.Quotient.mk _ w) = Ideal.Quotient.mk _ x → α n (Ideal.Quotient.mk _ w) = Ideal.Quotient.mk _ x) ∧
      (∀ (n : ℕ) (w : A') (x : ↥(FixedPoints.subalgebra S R' G)),
        α n (Ideal.Quotient.mk _ w) = Ideal.Quotient.mk _ x →
        τ n (Ideal.Quotient.mk _ ((1 : R) ⊗ₜ[↥(FixedPoints.subalgebra 𝒪 R G)] w)) = Ideal.Quotient.mk _ (x : R')) ∧
      (∀ (n : ℕ) (s : S),
        α n (Ideal.Quotient.mk _ (σ s)) = Ideal.Quotient.mk _ (algebraMap S ↥(FixedPoints.subalgebra S R' G) s)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_AdmissibleAlgebra_isAdicComplete_fixedPoints_and_exists_ringEquiv_quotient_of_ringEquiv_tensorProduct_quotient.solution
