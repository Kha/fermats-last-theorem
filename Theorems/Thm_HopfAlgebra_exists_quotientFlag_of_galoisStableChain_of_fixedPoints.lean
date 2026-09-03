import Mathlib
import P2M.Util
import P2M.Sol.S_HopfAlgebra_exists_quotientFlag_of_galoisStableChain_of_fixedPoints

theorem HopfAlgebra.exists_quotientFlag_of_galoisStableChain_of_fixedPoints
    {K : Type} [Field K] {L : Type} [Field L] [Algebra K L]
    (R : Type) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    [Algebra R L]
    (hR : Function.Injective (algebraMap R L))
    (hfix : ∀ c : L, (∀ σ : L ≃ₐ[K] L, (∀ r : R, σ (algebraMap R L r) = algebraMap R L r) → σ c = c) →
      ∃ a b : R, algebraMap R L b ≠ 0 ∧ c * algebraMap R L b = algebraMap R L a)
    (H : Type) [CommRing H] [HopfAlgebra R H] [Algebra.FiniteType R H] [Module.Flat R H]
    (M : Type) [AddCommGroup M] [Finite M]
    (e : WithConv (H →ₐ[R] L) ≃ M)
    (he : ∀ f g, e (f * g) = e f + e g)
    (act : (L ≃ₐ[K] L) → M → M)
    (hact : ∀ (σ : L ≃ₐ[K] L) (f g : WithConv (H →ₐ[R] L)),
        (∀ h : H, g h = σ (f h)) → e g = act σ (e f))
    (n : ℕ) (N : Fin (n + 1) → AddSubgroup M)
    (hmono : ∀ i : Fin n, N i.castSucc ≤ N i.succ)
    (htop : N (Fin.last n) = ⊤)
    (hstab : ∀ (i : Fin (n + 1)) (σ : L ≃ₐ[K] L) (x : M), x ∈ N i → act σ x ∈ N i) :
    ∃ (B : Fin (n + 1) → Type) (_ : ∀ i, CommRing (B i)) (_ : ∀ i, HopfAlgebra R (B i))
      (π : ∀ i, H →ₐc[R] B i) (φ : ∀ i : Fin n, B i.succ →ₐc[R] B i.castSucc),
      (∀ i, Algebra.FiniteType R (B i)) ∧ (∀ i, Module.Flat R (B i)) ∧
      (∀ i, Function.Surjective (π i)) ∧ (∀ i, Function.Surjective (φ i)) ∧
      (∀ i : Fin n, (φ i).comp (π i.succ) = π i.castSucc) ∧
      Function.Bijective (π (Fin.last n)) ∧
      (∀ (i : Fin (n + 1)) (f : H →ₐ[R] L),
        (∃ g : B i →ₐ[R] L, g.comp (π i : H →ₐ[R] B i) = f) ↔
          e (WithConv.toConv f) ∈ N i) ∧
      (Coalgebra.IsCocomm R H → ∀ i, Coalgebra.IsCocomm R (B i)) ∧
      (Module.Finite R H → ∀ i, Module.Finite R (B i) ∧
        (i ≠ Fin.last n → Module.finrank R (B i) = Nat.card (N i))) := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_exists_quotientFlag_of_galoisStableChain_of_fixedPoints.solution
