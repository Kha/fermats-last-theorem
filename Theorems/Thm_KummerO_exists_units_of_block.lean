import Mathlib
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_KummerO_exists_units_of_block

local notation "Γℚ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

theorem KummerO.exists_units_of_block
    (q : ℕ) [Fact q.Prime] (hq2 : q ≠ 2)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (hirr : Irreducible (q : O))
    [Algebra O ↥A] (ι : O →+* ↥A) (hι : Function.Injective ι) (hιalg : ∀ x : O, algebraMap O ↥A x = ι x)
    (hιfix : ∀ σ : Γℚ, σ ∈ A.inertiaSubgroupIn ℚ ↔ ∀ x : O, σ ((ι x : ↥A) : AlgebraicClosure ℚ) = ((ι x : ↥A) : AlgebraicClosure ℚ))
    (hιmax : ∀ a : ↥A, (∀ σ ∈ A.inertiaSubgroupIn ℚ, σ (a : AlgebraicClosure ℚ) = (a : AlgebraicClosure ℚ)) → a ∈ Set.range ι)
    (B : Type) [CommRing B] [HopfAlgebra O B] [Module.Finite O B] [Module.Free O B] [Coalgebra.IsCocomm O B]
    (hBq : ∀ (T : Type) [CommRing T] [Algebra O T] (f : WithConv (B →ₐ[O] T)), f ^ q = 1)
    (Λ : Type) [AddCommGroup Λ] [Fintype Λ] [DecidableEq Λ] (hΛq : ∀ g : Λ, q • g = 0)
    (p₀ : B →ₐc[O] MonoidAlgebra O (Multiplicative Λ)) (hsurj : Function.Surjective p₀)
    (e : B) (hidem : IsIdempotentElem e) (hcounit : Coalgebra.counit (R := O) e = 0)
    (hcard : Nat.card {ψ : WithConv (B →ₐ[O] ↥A) // ψ e = 1} = Fintype.card Λ)
    (hne : ∃ ψ : WithConv (B →ₐ[O] ↥A), ψ e = 1) :
    ∃ (U β : Λ → AlgebraicClosure ℚ),
      (∀ g, A.valuation (U g) = 1) ∧
      (∀ g, ∀ σ ∈ A.inertiaSubgroupIn ℚ, σ (U g) = U g) ∧
      (∀ g, (β g) ^ q = U g) ∧
      (∀ σ ∈ A.inertiaSubgroupIn ℚ, (∀ ζ : AlgebraicClosure ℚ, ζ ^ q = 1 → σ ζ = ζ) → (∀ g, σ (β g) = β g) →
        ∀ ψ : WithConv (B →ₐ[O] ↥A), ψ e = 1 → ∀ b : B, σ ((WithConv.ofConv ψ b : ↥A) : AlgebraicClosure ℚ) = ((WithConv.ofConv ψ b : ↥A) : AlgebraicClosure ℚ)) := by p2m_exact_reverting @_root_.P2MW.S_KummerO_exists_units_of_block.solution
