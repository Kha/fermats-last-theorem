import Mathlib
import Definitions.Def_ModularCurve_IgusaScheme
import P2M.Util
import P2M.Sol.S_ModularCurve_IgusaScheme_subfieldClosure_range_germToFunctionField_union_range_eq_top
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve

theorem ModularCurve.IgusaScheme.subfieldClosure_range_germToFunctionField_union_range_eq_top
    (N ℓ : ℕ) [NeZero N] [Fact ℓ.Prime] (S : Type) [CommRing S] (ρ : ↥(GaloisRep.ratLocalizedAt ℓ) →+* S)
    [hint : IsIntegral (pullback (IgusaScheme.igusaTo N ℓ) (Spec.map (CommRingCat.ofHom ρ)))]
    (x : ↥(pullback (IgusaScheme.igusaTo N ℓ) (Spec.map (CommRingCat.ofHom ρ))))
    [hne : Nonempty (Scheme.Opens.toScheme ((pullback.fst (IgusaScheme.igusaTo N ℓ) (Spec.map (CommRingCat.ofHom ρ))) ⁻¹ᵁ ((IgusaScheme.ιFin N ℓ) ''ᵁ ⊤)))] :
    Subfield.closure
      (Set.range (fun a : ↥(IgusaScheme.chartAlgFin N ℓ) =>
        ((pullback (IgusaScheme.igusaTo N ℓ) (Spec.map (CommRingCat.ofHom ρ))).germToFunctionField ((pullback.fst (IgusaScheme.igusaTo N ℓ) (Spec.map (CommRingCat.ofHom ρ))) ⁻¹ᵁ ((IgusaScheme.ιFin N ℓ) ''ᵁ ⊤))
            (((pullback.fst (IgusaScheme.igusaTo N ℓ) (Spec.map (CommRingCat.ofHom ρ))).app ((IgusaScheme.ιFin N ℓ) ''ᵁ ⊤)).hom
              (((IgusaScheme.ιFin N ℓ).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(IgusaScheme.chartAlgFin N ℓ))).inv a))))) ∪
        Set.range (fun s : S =>
          algebraMap ((pullback (IgusaScheme.igusaTo N ℓ) (Spec.map (CommRingCat.ofHom ρ))).presheaf.stalk x) ↥((pullback (IgusaScheme.igusaTo N ℓ) (Spec.map (CommRingCat.ofHom ρ))).functionField)
            (((pullback (IgusaScheme.igusaTo N ℓ) (Spec.map (CommRingCat.ofHom ρ))).presheaf.germ ⊤ x trivial).hom
              (((pullback.snd (IgusaScheme.igusaTo N ℓ) (Spec.map (CommRingCat.ofHom ρ))).appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of S)).inv s))))) = ⊤ := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_IgusaScheme_subfieldClosure_range_germToFunctionField_union_range_eq_top.solution
