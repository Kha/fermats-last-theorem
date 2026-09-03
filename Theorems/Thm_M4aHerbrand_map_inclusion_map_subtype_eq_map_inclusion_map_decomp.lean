import Mathlib
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_NumberField_PlaceDecompositionAction
import P2M.Util
import P2M.Sol.S_M4aHerbrand_map_inclusion_map_subtype_eq_map_inclusion_map_decomp
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory NumberField IsDedekindDomain M4aHerbrand
open scoped NumberField.PlaceDecomp

theorem M4aHerbrand.map_inclusion_map_subtype_eq_map_inclusion_map_decomp
    (E M : Type) [Field E] [NumberField E] [Field M] [NumberField M] [Algebra E M] [IsGalois E M]
    [MulDistribMulAction (M ≃ₐ[E] M) (AdeleRing (𝓞 M) M)ˣ]
    (S : Subgroup (M ≃ₐ[E] M)) (W : HeightOneSpectrum (𝓞 M))
    (prH : Rep.res (Subgroup.inclusion (inf_le_left : S ⊓ NumberField.PlaceDecomp.decomp E M W ≤ S))
          (Rep.res S.subtype (Rep.ofMulDistribMulAction (M ≃ₐ[E] M) (AdeleRing (𝓞 M) M)ˣ)) ⟶
        Rep.res (Subgroup.inclusion (inf_le_right : S ⊓ NumberField.PlaceDecomp.decomp E M W ≤ NumberField.PlaceDecomp.decomp E M W))
          (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E M W)) (W.adicCompletion M)ˣ))
    (hprH : ∀ x : (AdeleRing (𝓞 M) M)ˣ, prH.hom (Additive.ofMul x) = Additive.ofMul (finPart W x))
    (prM : Rep.res (NumberField.PlaceDecomp.decomp E M W).subtype (Rep.ofMulDistribMulAction (M ≃ₐ[E] M) (AdeleRing (𝓞 M) M)ˣ) ⟶
        Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E M W)) (W.adicCompletion M)ˣ)
    (hprM : ∀ x : (AdeleRing (𝓞 M) M)ˣ, prM.hom (Additive.ofMul x) = Additive.ofMul (finPart W x))
    (n : ℕ) (x : groupCohomology (Rep.ofMulDistribMulAction (M ≃ₐ[E] M) (AdeleRing (𝓞 M) M)ˣ) n) :
    (groupCohomology.map (Subgroup.inclusion (inf_le_left : S ⊓ NumberField.PlaceDecomp.decomp E M W ≤ S)) prH n).hom
        ((groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype (Rep.ofMulDistribMulAction (M ≃ₐ[E] M) (AdeleRing (𝓞 M) M)ˣ))) n).hom x) =
      (groupCohomology.map (Subgroup.inclusion (inf_le_right : S ⊓ NumberField.PlaceDecomp.decomp E M W ≤ NumberField.PlaceDecomp.decomp E M W))
          (𝟙 (Rep.res (Subgroup.inclusion (inf_le_right : S ⊓ NumberField.PlaceDecomp.decomp E M W ≤ NumberField.PlaceDecomp.decomp E M W))
            (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E M W)) (W.adicCompletion M)ˣ))) n).hom
        ((groupCohomology.map (NumberField.PlaceDecomp.decomp E M W).subtype prM n).hom x) := by p2m_exact_reverting @_root_.P2MW.S_M4aHerbrand_map_inclusion_map_subtype_eq_map_inclusion_map_decomp.solution
