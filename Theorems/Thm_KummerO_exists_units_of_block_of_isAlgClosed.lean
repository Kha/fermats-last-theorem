import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_KummerO_exists_units_of_block_of_isAlgClosed

set_option autoImplicit false

theorem KummerO.exists_units_of_block_of_isAlgClosed
    (q : ℕ) [Fact q.Prime] (hq2 : q ≠ 2)
    {K : Type} [Field K] {L : Type} [Field L] [Algebra K L] [IsAlgClosed L] [CharZero L]
    (A : ValuationSubring L) (hA : A.LiesOverPrime q)
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (hirr : Irreducible (q : O))
    [Algebra O ↥A] (ι : O →+* ↥A) (hι : Function.Injective ι) (hιalg : ∀ x : O, algebraMap O ↥A x = ι x)
    (hιfix : ∀ σ : (L ≃ₐ[K] L), σ ∈ A.inertiaSubgroupIn K ↔ ∀ x : O, σ ((ι x : ↥A) : L) = ((ι x : ↥A) : L))
    (hιmax : ∀ a : ↥A, (∀ σ ∈ A.inertiaSubgroupIn K, σ (a : L) = (a : L)) → a ∈ Set.range ι)
    (B : Type) [CommRing B] [HopfAlgebra O B] [Module.Finite O B] [Module.Free O B] [Coalgebra.IsCocomm O B]
    (hBq : ∀ (T : Type) [CommRing T] [Algebra O T] (f : WithConv (B →ₐ[O] T)), f ^ q = 1)
    (Λ : Type) [AddCommGroup Λ] [Fintype Λ] [DecidableEq Λ] (hΛq : ∀ g : Λ, q • g = 0)
    (p₀ : B →ₐc[O] MonoidAlgebra O (Multiplicative Λ)) (hsurj : Function.Surjective p₀)
    (e : B) (hidem : IsIdempotentElem e) (hcounit : Coalgebra.counit (R := O) e = 0)
    (hcard : Nat.card {ψ : WithConv (B →ₐ[O] ↥A) // ψ e = 1} = Fintype.card Λ)
    (hne : ∃ ψ : WithConv (B →ₐ[O] ↥A), ψ e = 1) :
    ∃ (U β : Λ → L),
      (∀ g, A.valuation (U g) = 1) ∧
      (∀ g, ∀ σ ∈ A.inertiaSubgroupIn K, σ (U g) = U g) ∧
      (∀ g, (β g) ^ q = U g) ∧
      (∀ σ ∈ A.inertiaSubgroupIn K, (∀ ζ : L, ζ ^ q = 1 → σ ζ = ζ) → (∀ g, σ (β g) = β g) →
        ∀ ψ : WithConv (B →ₐ[O] ↥A), ψ e = 1 → ∀ b : B, σ ((WithConv.ofConv ψ b : ↥A) : L) = ((WithConv.ofConv ψ b : ↥A) : L)) := by p2m_exact_reverting @_root_.P2MW.S_KummerO_exists_units_of_block_of_isAlgClosed.solution
