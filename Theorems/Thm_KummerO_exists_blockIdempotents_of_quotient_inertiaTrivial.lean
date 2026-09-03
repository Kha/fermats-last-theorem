import Mathlib
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_KummerO_exists_blockIdempotents_of_quotient_inertiaTrivial
attribute [-instance] MonoidAlgebra.instModuleFiniteOfCartier CartierDual.instCoalgebra CartierDual.instModuleFinite CartierDual.instBialgebra CartierDual.instFunLike CartierDual.instRing CartierDual.instLinearMapClass CartierDual.instCommRing CartierDual.instIsCocomm MonoidAlgebra.instModuleFreeOfCartier CartierDual.instModuleFree CartierDual.instHopfAlgebra CartierDual.instAlgebra CartierDual.instIsCocommViaBialgebra CartierDual.instModuleFreeViaBialgebra CartierDual.instModuleFiniteViaBialgebra
attribute [-simp] CartierDual.toDual_ofDual CartierDual.algebraMap_apply CartierDual.antipode_apply CartierDual.one_apply CartierDual.toDual_apply CartierDual.ofDual_toDual CartierDual.ofDual_apply CartierDual.counit_apply CartierDual.map_apply CartierDual.congr_apply CartierDual.congr_symm_apply CartierDual.pairing_apply CartierDual.mapAlgHom_apply CartierDual.mapLinear_apply

local notation "Γℚ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

theorem KummerO.exists_blockIdempotents_of_quotient_inertiaTrivial
    (q : ℕ) [Fact q.Prime] (hq2 : q ≠ 2)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (hirr : Irreducible (q : O))
    [Algebra O ↥A] (ι : O →+* ↥A) (hι : Function.Injective ι) (hιalg : ∀ x : O, algebraMap O ↥A x = ι x)
    (hιfix : ∀ σ : Γℚ, σ ∈ A.inertiaSubgroupIn ℚ ↔ ∀ x : O, σ ((ι x : ↥A) : AlgebraicClosure ℚ) = ((ι x : ↥A) : AlgebraicClosure ℚ))
    (hιmax : ∀ a : ↥A, (∀ σ ∈ A.inertiaSubgroupIn ℚ, σ (a : AlgebraicClosure ℚ) = (a : AlgebraicClosure ℚ)) → a ∈ Set.range ι)
    (B : Type) [CommRing B] [HopfAlgebra O B] [Module.Finite O B] [Module.Free O B] [Coalgebra.IsCocomm O B]
    (hBq : ∀ (T : Type) [CommRing T] [Algebra O T] (f : WithConv (B →ₐ[O] T)), f ^ q = 1)
    (n : Γℚ → ℕ)
    (hn : ∀ σ (ζ : AlgebraicClosure ℚ), ζ ^ q = 1 → σ ζ = ζ ^ n σ)
    (D : Submonoid (WithConv (B →ₐ[O] ↥A)))
    (hDcyc : ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ f ∈ D, ∀ g : WithConv (B →ₐ[O] ↥A),
      (∀ b : B, ((WithConv.ofConv g b : ↥A) : AlgebraicClosure ℚ) = σ ((WithConv.ofConv f b : ↥A) : AlgebraicClosure ℚ)) → g = f ^ n σ)
    (hquot : ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ f g : WithConv (B →ₐ[O] ↥A),
      (∀ b : B, ((WithConv.ofConv g b : ↥A) : AlgebraicClosure ℚ) = σ ((WithConv.ofConv f b : ↥A) : AlgebraicClosure ℚ)) → ∃ d ∈ D, g = f * d)
    (Λ : Type) [AddCommGroup Λ] [Fintype Λ] [DecidableEq Λ] (hΛ : Nat.card Λ = Nat.card ↥D) :
    ∃ (N : ℕ) (ε : Fin (N + 1) → B),
      (∀ i, IsIdempotentElem (ε i)) ∧
      (∀ i j, i ≠ j → ε i * ε j = 0) ∧
      (∑ i, ε i) = 1 ∧
      Coalgebra.counit (R := O) (ε 0) = 1 ∧
      (∀ i, i ≠ 0 → Coalgebra.counit (R := O) (ε i) = 0) ∧
      (∀ ψ : WithConv (B →ₐ[O] ↥A), ∃! i : Fin (N + 1), ψ (ε i) = 1) ∧
      (∀ ψ : WithConv (B →ₐ[O] ↥A), ψ ∈ D ↔ ψ (ε 0) = 1) ∧
      (∀ i : Fin (N + 1), ∃ ψ : WithConv (B →ₐ[O] ↥A), ψ (ε i) = 1) ∧
      (∀ (i : Fin (N + 1)) (ψ φ : WithConv (B →ₐ[O] ↥A)), ψ (ε i) = 1 → (φ (ε i) = 1 ↔ ∃ d ∈ D, φ = ψ * d)) ∧
      (∀ i : Fin (N + 1), Nat.card {ψ : WithConv (B →ₐ[O] ↥A) // ψ (ε i) = 1} = Fintype.card Λ) ∧
      (N + 1) * Nat.card ↥D = Nat.card (WithConv (B →ₐ[O] ↥A)) := by p2m_exact_reverting @_root_.P2MW.S_KummerO_exists_blockIdempotents_of_quotient_inertiaTrivial.solution
