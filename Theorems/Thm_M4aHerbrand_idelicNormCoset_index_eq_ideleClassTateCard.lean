import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Mathlib.FieldTheory.Galois.Basic
import P2M.Util
import P2M.Sol.S_M4aHerbrand_idelicNormCoset_index_eq_ideleClassTateCard

set_option autoImplicit false
open NumberField M4aHerbrand

theorem M4aHerbrand.idelicNormCoset_index_eq_ideleClassTateCard
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L]
    (D : IdeleGaloisDescent (𝓞 L) K L)
    (β : AdeleRing (𝓞 K) K →+* AdeleRing (𝓞 L) L)
    (Nrm : (AdeleRing (𝓞 L) L)ˣ →* (AdeleRing (𝓞 K) K)ˣ)
    (σ : L ≃ₐ[K] L) (hσ : ∀ τ, τ ∈ Subgroup.zpowers σ)
    (hβ : ∀ x : K, β (algebraMap K (AdeleRing (𝓞 K) K) x)
      = algebraMap L (AdeleRing (𝓞 L) L) (algebraMap K L x))
    (hβinj : Function.Injective β)
    (hfix : ∀ u : (AdeleRing (𝓞 L) L)ˣ, (∀ τ : L ≃ₐ[K] L, D.unitsAct τ u = u)
      ↔ u ∈ (Units.map β.toMonoidHom).range)
    (h90 : ∀ u : (AdeleRing (𝓞 L) L)ˣ,
      (∀ τ : L ≃ₐ[K] L, (D.unitsAct τ u)⁻¹ * u ∈ principalIdeles (𝓞 L) L) →
      u ∈ (Units.map β.toMonoidHom).range ⊔ principalIdeles (𝓞 L) L)
    (hnorm : ∀ u : (AdeleRing (𝓞 L) L)ˣ,
      ∏ τ : L ≃ₐ[K] L, D.unitsAct τ u = Units.map β.toMonoidHom (Nrm u)) :
    (principalIdeles (𝓞 K) K ⊔ Nrm.range).index
      = Nat.card ((ideleClassDerive D σ).ker
          ⧸ ((ideleClassNorm D).range.subgroupOf (ideleClassDerive D σ).ker)) := by p2m_exact_reverting @_root_.P2MW.S_M4aHerbrand_idelicNormCoset_index_eq_ideleClassTateCard.solution
