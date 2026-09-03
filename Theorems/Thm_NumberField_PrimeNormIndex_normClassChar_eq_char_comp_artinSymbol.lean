import Definitions.Def_LanglandsTunnell_ArtinCoreCTM
import P2M.Util
import P2M.Sol.S_NumberField_PrimeNormIndex_normClassChar_eq_char_comp_artinSymbol

set_option autoImplicit false

open NumberField IsDedekindDomain Deep.NTSupply
open LanglandsTunnell.P2.Artin

theorem NumberField.PrimeNormIndex.normClassChar_eq_char_comp_artinSymbol
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [IsMulCommutative (L ≃ₐ[K] L)]
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hdeg : Module.finrank K L = ℓ)
    (𝔣 : Ideal (𝓞 K))
    (σ : L ≃ₐ[K] L) {Ip : Type*} [CommGroup Ip]
    (N : ↥(coprimeToModulus K 𝔣) → (Ip →* ↥(coprimeToModulus K 𝔣)))
    (ωp : ↥(coprimeToModulus K 𝔣) → (Ip →* (L ≃ₐ[K] L)))
    (P : ↥(coprimeToModulus K 𝔣) → Ip) (d : ↥(coprimeToModulus K 𝔣) → ℤ)
    (hcompat : ∀ p ∈ primeCarriers K 𝔣, ∀ x, artinSymbol K L 𝔣 (N p x) = ωp p x)
    (hker : ∀ p ∈ primeCarriers K 𝔣, ∀ x, ωp p x = 1 → N p x ∈ normRaySubgroup K L 𝔣)
    (hNP : ∀ p ∈ primeCarriers K 𝔣, N p (P p) = p)
    (hd : ∀ p ∈ primeCarriers K 𝔣, ωp p (P p) = σ ^ d p)
    (hcross : ∀ p ∈ primeCarriers K 𝔣, ∀ q ∈ primeCarriers K 𝔣,
      ∃ bp bq : Ip, N p bp = N q bq ∧ ωp p bp = σ)
    (ω : NarrowRayClassGroup K 𝔣 →* ℂˣ)
    (hω : ∀ (w : HeightOneSpectrum (𝓞 L)) (hw : ¬ ((w.under (𝓞 K)).asIdeal ∣ 𝔣)),
      ω (primeClass K 𝔣 (w.under (𝓞 K)) hw ^
        ((w.under (𝓞 K)).asIdeal.inertiaDeg' w.asIdeal)) = 1) :
    ∃ χ : (L ≃ₐ[K] L) →* ℂˣ,
      ω.comp (NarrowRayClassGroup.mk K 𝔣) = χ.comp (artinSymbol K L 𝔣) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_PrimeNormIndex_normClassChar_eq_char_comp_artinSymbol.solution
