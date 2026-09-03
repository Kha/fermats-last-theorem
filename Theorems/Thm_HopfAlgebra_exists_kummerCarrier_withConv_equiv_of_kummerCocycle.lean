import Mathlib
import P2M.Util
import P2M.Sol.S_HopfAlgebra_exists_kummerCarrier_withConv_equiv_of_kummerCocycle

set_option autoImplicit false

theorem HopfAlgebra.exists_kummerCarrier_withConv_equiv_of_kummerCocycle
    (O : Type) [CommRing O] [Nontrivial O] (p N : ℕ) [Fact p.Prime]
    (Λ : Type) [AddCommGroup Λ] [Finite Λ]
    (u : Λ → O) (hu : ∀ l : Λ, IsUnit (u l)) (hu0 : u 0 = 1)
    (c : Λ → Λ → O)
    (hc : ∀ l l' : Λ, c l l' ^ (p ^ N) * (u l * u l') = u (l + l'))
    (hc0 : ∀ l : Λ, c 0 l = 1) (hcomm : ∀ l l' : Λ, c l l' = c l' l)
    (hassoc : ∀ l l' l'' : Λ, c l l' * c (l + l') l'' = c l (l' + l'') * c l' l'') :
    ∃ (H : Type) (_ : CommRing H) (_ : HopfAlgebra O H),
      Module.Finite O H ∧ Module.Free O H ∧ Coalgebra.IsCocomm O H ∧
      Module.finrank O H = p ^ N * Nat.card Λ ∧
      ∀ (L : Type) [CommRing L] [IsDomain L] [Algebra O L] (ζ : L), IsPrimitiveRoot ζ (p ^ N) →
        ∀ η : Λ → L, (∀ l, η l ^ (p ^ N) = algebraMap O L (u l)) → η 0 = 1 →
          (∀ l l', η (l + l') = algebraMap O L (c l l') * η l * η l') →
          ∃ ψ : ZMod (p ^ N) × Λ ≃ WithConv (H →ₐ[O] L),
            (∀ a b, ψ (a + b) = ψ a * ψ b) ∧
            ∀ (τ : L →ₐ[O] L) (e : ℕ) (κ : Λ → ℕ), τ ζ = ζ ^ e → (∀ l, τ (η l) = ζ ^ κ l * η l) →
              ∀ (i : ZMod (p ^ N)) (l : Λ) (h : H), ψ (e • i + (κ l : ZMod (p ^ N)), l) h = τ (ψ (i, l) h) := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_exists_kummerCarrier_withConv_equiv_of_kummerCocycle.solution
