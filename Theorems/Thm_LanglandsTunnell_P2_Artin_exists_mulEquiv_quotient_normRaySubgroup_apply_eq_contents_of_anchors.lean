import Definitions.Def_LanglandsTunnell_ArtinCoreCTM
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_P2_Artin_exists_mulEquiv_quotient_normRaySubgroup_apply_eq_contents_of_anchors

set_option autoImplicit false

open NumberField

theorem LanglandsTunnell.P2.Artin.exists_mulEquiv_quotient_normRaySubgroup_apply_eq_contents_of_anchors
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (𝔣 : Ideal (𝓞 K)) (h𝔣 : 𝔣 ≠ ⊥)
    (Nrm : (AdeleRing (𝓞 L) L)ˣ →* (AdeleRing (𝓞 K) K)ˣ)
    (hA1 : ∀ {u : (AdeleRing (𝓞 L) L)ˣ} {α : Lˣ},
      HeckeCharacter.IsAdjuster L (HeckeCharacter.modulusExt K L 𝔣) u α →
        HeckeCharacter.IsAdjuster K 𝔣 (Nrm u) (Units.map (Algebra.norm K) α))
    (hA2 : ∀ u : (AdeleRing (𝓞 L) L)ˣ,
      HeckeCharacter.fadContentHom K (HeckeCharacter.projFin K (Nrm u)) =
        HeckeCharacter.fracRelNormUnit K L
          (HeckeCharacter.fadContentHom L (HeckeCharacter.projFin L u)))
    (hA3 : LanglandsTunnell.P2.Artin.unitIdeles K 𝔣 ≤ Nrm.range) :
    ∃ φ : (AdeleRing (𝓞 K) K)ˣ ⧸ (M4aHerbrand.principalIdeles (𝓞 K) K ⊔ Nrm.range) ≃*
        ↥(Deep.NTSupply.coprimeToModulus K 𝔣) ⧸ LanglandsTunnell.P2.Artin.normRaySubgroup K L 𝔣,
      ∀ (u : (AdeleRing (𝓞 K) K)ˣ) (hu : HeckeCharacter.IsAdjuster K 𝔣 u 1)
        (hc : HeckeCharacter.fadContentHom K (HeckeCharacter.projFin K u) ∈
          Deep.NTSupply.coprimeToModulus K 𝔣),
        φ (QuotientGroup.mk u) =
          QuotientGroup.mk ⟨HeckeCharacter.fadContentHom K (HeckeCharacter.projFin K u), hc⟩ := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_P2_Artin_exists_mulEquiv_quotient_normRaySubgroup_apply_eq_contents_of_anchors.solution
