import Mathlib
import P2M.Util
import P2M.Sol.S_IsLocalRing_exists_ringHom_forall_existsUnique_algHom_comp_eq_of_isAdicComplete

set_option autoImplicit false

open IsLocalRing in

theorem IsLocalRing.exists_ringHom_forall_existsUnique_algHom_comp_eq_of_isAdicComplete
    (O : Type) [CommRing O] [IsLocalRing O]
    (S : Type) [CommRing S] (xbar : S →+* ResidueField O)
    (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [Algebra O R]
    [IsAdicComplete (maximalIdeal R) R]
    (resR : R →+* ResidueField O) (hresR : resR.comp (algebraMap O R) = residue O)
    (β : ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsArtinianRing A] [Algebra O A]
        (resA : A →+* ResidueField O), Function.Surjective resA →
        resA.comp (algebraMap O A) = residue O →
        ∀ ψ : S →+* A, resA.comp ψ = xbar → (R →ₐ[O] A))
    (hβ_res : ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsArtinianRing A] [Algebra O A]
        (resA : A →+* ResidueField O) (hs : Function.Surjective resA)
        (hc : resA.comp (algebraMap O A) = residue O) (ψ : S →+* A) (hψ : resA.comp ψ = xbar),
        resA.comp (β A resA hs hc ψ hψ).toRingHom = resR)
    (hβ_inj : ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsArtinianRing A] [Algebra O A]
        (resA : A →+* ResidueField O) (hs : Function.Surjective resA)
        (hc : resA.comp (algebraMap O A) = residue O)
        (ψ₁ : S →+* A) (hψ₁ : resA.comp ψ₁ = xbar) (ψ₂ : S →+* A) (hψ₂ : resA.comp ψ₂ = xbar),
        β A resA hs hc ψ₁ hψ₁ = β A resA hs hc ψ₂ hψ₂ → ψ₁ = ψ₂)
    (hβ_surj : ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsArtinianRing A] [Algebra O A]
        (resA : A →+* ResidueField O) (hs : Function.Surjective resA)
        (hc : resA.comp (algebraMap O A) = residue O) (χ : R →ₐ[O] A),
        resA.comp χ.toRingHom = resR → ∃ (ψ : S →+* A) (hψ : resA.comp ψ = xbar), β A resA hs hc ψ hψ = χ)
    (hβ_nat : ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsArtinianRing A] [Algebra O A]
        (resA : A →+* ResidueField O) (hs : Function.Surjective resA)
        (hc : resA.comp (algebraMap O A) = residue O)
        (A' : Type) [CommRing A'] [IsLocalRing A'] [IsArtinianRing A'] [Algebra O A']
        (resA' : A' →+* ResidueField O) (hs' : Function.Surjective resA')
        (hc' : resA'.comp (algebraMap O A') = residue O)
        (f : A →ₐ[O] A'), resA'.comp f.toRingHom = resA →
        ∀ (ψ : S →+* A) (hψ : resA.comp ψ = xbar) (hψ' : resA'.comp (f.toRingHom.comp ψ) = xbar),
        β A' resA' hs' hc' (f.toRingHom.comp ψ) hψ' = f.comp (β A resA hs hc ψ hψ)) :
    ∃ φ : S →+* R, resR.comp φ = xbar ∧
      (∀ (A : Type) [CommRing A] [IsLocalRing A] [IsArtinianRing A] [Algebra O A]
          (resA : A →+* ResidueField O), Function.Surjective resA →
          resA.comp (algebraMap O A) = residue O →
        ∀ ψ : S →+* A, resA.comp ψ = xbar →
          ∃! χ : R →ₐ[O] A, resA.comp χ.toRingHom = resR ∧ χ.toRingHom.comp φ = ψ) ∧
      (∀ (A : Type) [CommRing A] [IsLocalRing A] [IsArtinianRing A] [Algebra O A]
          (resA : A →+* ResidueField O) (hs : Function.Surjective resA)
          (hc : resA.comp (algebraMap O A) = residue O) (ψ : S →+* A) (hψ : resA.comp ψ = xbar),
        (β A resA hs hc ψ hψ).toRingHom.comp φ = ψ) := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_exists_ringHom_forall_existsUnique_algHom_comp_eq_of_isAdicComplete.solution
