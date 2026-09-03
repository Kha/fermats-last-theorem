import Mathlib
import P2M.Util
import P2M.Sol.S_HopfAlgebra_exists_quotientFlag_of_galoisStableChain

theorem HopfAlgebra.exists_quotientFlag_of_galoisStableChain
    (R : Type) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    [Algebra R (AlgebraicClosure ℚ)]
    (hR : Function.Injective (algebraMap R (AlgebraicClosure ℚ)))
    (H : Type) [CommRing H] [HopfAlgebra R H] [Algebra.FiniteType R H] [Module.Flat R H]
    (M : Type) [AddCommGroup M] [Finite M]
    (e : WithConv (H →ₐ[R] AlgebraicClosure ℚ) ≃ M)
    (he : ∀ f g, e (f * g) = e f + e g)
    (act : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → M → M)
    (hact : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
        (f g : WithConv (H →ₐ[R] AlgebraicClosure ℚ)),
        (∀ h : H, g h = σ (f h)) → e g = act σ (e f))
    (n : ℕ) (N : Fin (n + 1) → AddSubgroup M)
    (hmono : ∀ i : Fin n, N i.castSucc ≤ N i.succ)
    (htop : N (Fin.last n) = ⊤)
    (hstab : ∀ (i : Fin (n + 1)) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : M),
        x ∈ N i → act σ x ∈ N i) :
    ∃ (B : Fin (n + 1) → Type) (_ : ∀ i, CommRing (B i)) (_ : ∀ i, HopfAlgebra R (B i))
      (π : ∀ i, H →ₐc[R] B i) (φ : ∀ i : Fin n, B i.succ →ₐc[R] B i.castSucc),
      (∀ i, Algebra.FiniteType R (B i)) ∧ (∀ i, Module.Flat R (B i)) ∧
      (∀ i, Function.Surjective (π i)) ∧ (∀ i, Function.Surjective (φ i)) ∧
      (∀ i : Fin n, (φ i).comp (π i.succ) = π i.castSucc) ∧
      Function.Bijective (π (Fin.last n)) ∧
      (∀ (i : Fin (n + 1)) (f : H →ₐ[R] AlgebraicClosure ℚ),
        (∃ g : B i →ₐ[R] AlgebraicClosure ℚ, g.comp (π i : H →ₐ[R] B i) = f) ↔
          e (WithConv.toConv f) ∈ N i) ∧
      (Coalgebra.IsCocomm R H → ∀ i, Coalgebra.IsCocomm R (B i)) ∧
      (Module.Finite R H → ∀ i, Module.Finite R (B i) ∧
        (i ≠ Fin.last n → Module.finrank R (B i) = Nat.card (N i))) := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_exists_quotientFlag_of_galoisStableChain.solution
