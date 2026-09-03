import Definitions.Def_CuspForm_HeckeGaloisRepDatum
import Definitions.Def_GaloisRep_DeformationRingData
import Theorems.Thm_CuspForm_HeckeGaloisRepDatum_surjective_of_isEquiv_baseChangeAlong
import P2M.Util
namespace P2MW.S_GaloisRep_DeformationRingData_exists_surjective_algHom_of_heckeGaloisRepDatum

theorem solution {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪] {ρbar : ResidualGaloisRep (IsLocalRing.ResidueField 𝒪)} {𝒟 : ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A], GaloisRepAdic A → Prop} (D : GaloisRep.DeformationRingData 𝒪 ρbar 𝒟) {N : ℕ} [NeZero N] {S : Set ℕ} {θ : CuspForm.heckeAlgebra N 2 S →+* IsLocalRing.ResidueField 𝒪} {T : Type} [CommRing T] [IsLocalRing T] [IsNoetherianRing T] [IsAdicComplete (IsLocalRing.maximalIdeal T) T] [Algebra 𝒪 T] [IsLocalHom (algebraMap 𝒪 T)] [Module.Finite 𝒪 T] [Module.Free 𝒪 T] (H : CuspForm.HeckeGaloisRepDatum N S 𝒪 θ T) (hS : ∀ q : ℕ, q.Prime → q ∣ N → q ∈ S) (h𝒟 : 𝒟 H.ρ) (hres : H.ρ.residual.IsEquiv (ρbar.baseChangeAlong (IsLocalRing.ResidueField.map (algebraMap 𝒪 T)))) : ∃ φ : D.R →ₐ[𝒪] T, Function.Surjective φ ∧ ∃ hφ : IsLocalHom (φ : D.R →+* T), (D.ρ.baseChangeAlong (φ : D.R →+* T) hφ).IsEquiv H.ρ := by
  obtain ⟨φ, ⟨hφ, he⟩, -⟩ := D.universal T H.residue_surjective H.ρ h𝒟 hres
  exact ⟨φ, H.surjective_of_isEquiv_baseChangeAlong hS D.ρ φ hφ he, hφ, he⟩
