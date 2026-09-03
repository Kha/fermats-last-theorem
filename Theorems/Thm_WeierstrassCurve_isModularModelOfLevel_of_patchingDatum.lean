import Definitions.Def_GaloisRep_DeformationRingData
import Definitions.Def_CuspForm_HeckeGaloisRepDatum
import Definitions.Def_Algebra_PatchingDatum
import Definitions.Def_CuspForm_IntegralStructure
import Definitions.Def_FLTPrelim_ModularRep
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_isModularModelOfLevel_of_patchingDatum

open Polynomial

theorem WeierstrassCurve.isModularModelOfLevel_of_patchingDatum (p : ℕ) (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0) {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪] [Finite (IsLocalRing.ResidueField 𝒪)] [CharZero 𝒪] (hp𝒪 : (p : 𝒪) ∈ IsLocalRing.maximalIdeal 𝒪) {ρbar : ResidualGaloisRep (IsLocalRing.ResidueField 𝒪)} {𝒟 : ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A], GaloisRepAdic A → Prop} (D : GaloisRep.DeformationRingData 𝒪 ρbar 𝒟) {N : ℕ} [NeZero N] {S : Finset ℕ} (hSprime : ∀ q ∈ S, q.Prime) (hNS : ∀ q : ℕ, q.Prime → q ∣ N → q ∈ S) (hN : CuspForm.HasIntegralStructure N 2) {θ : CuspForm.heckeAlgebra N 2 (S : Set ℕ) →+* IsLocalRing.ResidueField 𝒪} {T : Type} [CommRing T] [IsLocalRing T] [IsNoetherianRing T] [IsAdicComplete (IsLocalRing.maximalIdeal T) T] [Algebra 𝒪 T] [IsLocalHom (algebraMap 𝒪 T)] [Module.Finite 𝒪 T] [Module.Free 𝒪 T] (H : CuspForm.HeckeGaloisRepDatum N (S : Set ℕ) 𝒪 θ T) (φ : D.R →ₐ[𝒪] T) (hφ : IsLocalHom (φ : D.R →+* T)) (hφρ : (D.ρ.baseChangeAlong (φ : D.R →+* T) hφ).IsEquiv H.ρ) {M : Type} [AddCommGroup M] [Module D.R M] [Module T M] [Nontrivial M] (hcompat : ∀ (x : D.R) (m : M), φ x • m = x • m) {r : ℕ} (P : Algebra.PatchingDatum 𝒪 p r D.R M) (ρW : GaloisRepAdic 𝒪) (h𝒟W : 𝒟 ρW) (hWres : ρW.residual.IsEquiv (ρbar.baseChangeAlong (IsLocalRing.ResidueField.map (algebraMap 𝒪 𝒪)))) (hWfrob : ∀ (ℓ : ℕ), ℓ.Prime → W.IsGoodPrimeFor ℓ → ℓ ∉ S → ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ → ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ → LinearMap.charpoly (ρW.ρ σ) = X ^ 2 - C ((W.apOfModel ℓ : ℤ) : 𝒪) * X + C ((ℓ : 𝒪))) :
    W.IsModularModelOfLevel (N * ∏ q ∈ S.filter (fun q => ¬ q ∣ N), q) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_isModularModelOfLevel_of_patchingDatum.solution
