import Definitions.Def_GaloisRep_Flat
import Definitions.Def_GaloisRep_TameCharacter
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_HopfAlgebra_exists_inertiaStable_simple_step_of_map_ne_zero
attribute [-instance] instIsScalarTowerTensorProduct_definitions
attribute [-simp] closureCounit_apply genericFibreAlgHom_tmul tensorInclusion_closureComul coe_closureAntipode_apply tensorToGenericFibre_tmul tensorInclusion_tmul mem_flatClosure_iff

theorem HopfAlgebra.exists_inertiaStable_simple_step_of_map_ne_zero
    {p : ℕ} (hp : p.Prime)
    {H : Type} [CommRing H] [HopfAlgebra (GaloisRep.ratLocalizedAt p) H]
    [Module.Finite (GaloisRep.ratLocalizedAt p) H] [Module.Flat (GaloisRep.ratLocalizedAt p) H]
    [Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt p) H]
    (hMp : ∀ f : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ), f ^ p = 1)
    (P : ValuationSubring (AlgebraicClosure ℚ))
    (N : Type) [AddCommGroup N]
    (F : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) → N)
    (hFmul : ∀ f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ),
      F (f * g) = F f + F g)
    (K₀ : Submonoid (WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)))
    (hK₀ : (∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ f ∈ K₀,
      ∀ g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ),
        (∀ h : H, g h = σ (f h)) → g ∈ K₀))
    (hFK₀ : ∃ f ∈ K₀, F f ≠ 0) :
    ∃ K K' : Submonoid (WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
      K ≤ K' ∧ K' ≤ K₀ ∧
      (∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ f ∈ K,
        ∀ g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ),
          (∀ h : H, g h = σ (f h)) → g ∈ K) ∧
      (∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ f ∈ K',
        ∀ g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ),
          (∀ h : H, g h = σ (f h)) → g ∈ K') ∧
      (∀ S : Submonoid (WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
        K ≤ S → S ≤ K' →
        (∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ f ∈ S,
          ∀ g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ),
            (∀ h : H, g h = σ (f h)) → g ∈ S) →
        S = K ∨ S = K') ∧
      (∀ f ∈ K, F f = 0) ∧ (∃ f ∈ K', F f ≠ 0) ∧
      ∃ s : ℕ, 1 ≤ s ∧ Nat.card K' = p ^ s * Nat.card K := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_exists_inertiaStable_simple_step_of_map_ne_zero.solution
