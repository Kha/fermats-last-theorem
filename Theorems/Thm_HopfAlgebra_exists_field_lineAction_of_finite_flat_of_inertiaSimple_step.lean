import Definitions.Def_GaloisRep_Flat
import Definitions.Def_GaloisRep_TameCharacter
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_HopfAlgebra_exists_field_lineAction_of_finite_flat_of_inertiaSimple_step

theorem HopfAlgebra.exists_field_lineAction_of_finite_flat_of_inertiaSimple_step
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {H : Type} [CommRing H] [HopfAlgebra (GaloisRep.ratLocalizedAt p) H]
    [Module.Finite (GaloisRep.ratLocalizedAt p) H] [Module.Flat (GaloisRep.ratLocalizedAt p) H]
    [Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt p) H]
    (hMp : ∀ f : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ), f ^ p = 1)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime p)
    (K K' : Submonoid (WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)))
    (hKK' : K ≤ K')
    (hK : (∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ f ∈ K,
      ∀ g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ),
        (∀ h : H, g h = σ (f h)) → g ∈ K))
    (hK' : (∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ f ∈ K',
      ∀ g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ),
        (∀ h : H, g h = σ (f h)) → g ∈ K'))
    (hstep : ∀ S : Submonoid (WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
      K ≤ S → S ≤ K' →
      (∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ f ∈ S,
        ∀ g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ),
          (∀ h : H, g h = σ (f h)) → g ∈ S) →
      S = K ∨ S = K')
    (s : ℕ) [NeZero s] (hcard : Nat.card K' = p ^ s * Nat.card K) :
    ∃ (F : Type) (_ : Field F) (_ : Fintype F)
      (act : F → WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) →
        WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
      Fintype.card F = p ^ s ∧
      (∀ a : F, ∀ f ∈ K', act a f ∈ K') ∧
      (∀ a : F, ∀ f ∈ K', ∀ k ∈ K, ∃ k' ∈ K, act a (f * k) = act a f * k') ∧
      (∀ a : F, ∀ f ∈ K', ∀ g ∈ K', ∃ k ∈ K, act a (f * g) = act a f * act a g * k) ∧
      (∀ a b : F, ∀ f ∈ K', ∃ k ∈ K, act (a + b) f = act a f * act b f * k) ∧
      (∀ a b : F, ∀ f ∈ K', ∃ k ∈ K, act (a * b) f = act a (act b f) * k) ∧
      (∀ f ∈ K', ∃ k ∈ K, act 1 f = f * k) ∧
      (∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ a : F, ∀ f ∈ K',
        ∀ g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ),
          (∀ h : H, g h = σ (f h)) → ∃ k ∈ K, ∀ h : H, (act a g * k) h = σ ((act a f) h)) ∧
      (∀ f₀ ∈ K', f₀ ∉ K → ∀ g ∈ K', ∃ a : F, ∃ k ∈ K, g = act a f₀ * k) ∧
      (∀ f₀ ∈ K', f₀ ∉ K → ∀ a b : F, (∃ k ∈ K, act a f₀ = act b f₀ * k) → a = b) := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_exists_field_lineAction_of_finite_flat_of_inertiaSimple_step.solution
