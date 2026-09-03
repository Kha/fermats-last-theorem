import Definitions.Def_CuspForm_HeckeGaloisRepDatum
import Definitions.Def_GaloisRep_LocalConditions
import P2M.Util
import P2M.Sol.S_CuspForm_HeckeGaloisRepDatum_false_of_isOrdinaryAt_of_forall_decompositionStable_eq_bot_or_top
attribute [-instance] FrobeniusDensity.isMaximal_ratPrimeIdeal AlgebraicClosure.Rat.isGalois FrobeniusDensity.liesOver_ratBelow
attribute [-simp] TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec

open Polynomial

variable {N : ℕ} [NeZero N] {S : Finset ℕ}
  {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
  {θ : CuspForm.heckeAlgebra N 2 (↑S : Set ℕ) →+* IsLocalRing.ResidueField 𝒪}
  {T : Type} [CommRing T] [IsLocalRing T] [IsNoetherianRing T]
  [IsAdicComplete (IsLocalRing.maximalIdeal T) T] [Algebra 𝒪 T] [IsLocalHom (algebraMap 𝒪 T)]
  [Module.Finite 𝒪 T] [Module.Free 𝒪 T]
theorem CuspForm.HeckeGaloisRepDatum.false_of_isOrdinaryAt_of_forall_decompositionStable_eq_bot_or_top
    (H : CuspForm.HeckeGaloisRepDatum N (↑S : Set ℕ) 𝒪 θ T) {p : ℕ} (hp : p.Prime)
    (hres : (GaloisRepAdic.ofResidualGaloisRep H.ρ.residual).IsOrdinaryAt p)
    {𝒪' : Type} [CommRing 𝒪'] [IsLocalRing 𝒪']
    (e : IsLocalRing.ResidueField 𝒪 →+* IsLocalRing.ResidueField 𝒪')
    (χ : CuspForm.heckeAlgebra N 2 (↑S : Set ℕ) →+* 𝒪')
    (hχ : ∀ t : CuspForm.heckeAlgebra N 2 (↑S : Set ℕ), IsLocalRing.residue 𝒪' (χ t) = e (θ t))
    (ρ : GaloisRepAdic 𝒪')
    (hfrob : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ S),
        ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
          ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
            LinearMap.charpoly (ρ.ρ σ) =
              X ^ 2 - C (χ (CuspForm.heckeAlgebra.T hℓ hℓN hℓS)) * X + C ((ℓ : 𝒪')))
    (hnsl : ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime p →
        ∀ L : Submodule (IsLocalRing.ResidueField 𝒪') ρ.residual.V,
          (∀ σ ∈ P.decompositionSubgroup ℚ, ∀ v ∈ L, ρ.residual.ρ σ v ∈ L) → L = ⊥ ∨ L = ⊤) :
    False := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_HeckeGaloisRepDatum_false_of_isOrdinaryAt_of_forall_decompositionStable_eq_bot_or_top.solution
