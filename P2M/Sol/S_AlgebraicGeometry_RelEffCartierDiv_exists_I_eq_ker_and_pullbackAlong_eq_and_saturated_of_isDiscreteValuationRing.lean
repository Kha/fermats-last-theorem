import Mathlib
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_comap_ker_subschemeIota_comp_mapOnProdOver_eq_and_saturated_of_isDiscreteValuationRing
import Theorems.Thm_AlgebraicGeometry_IdealSheafData_flat_subschemeInclusion_comp_of_forall_mul_mem_of_isDiscreteValuationRing
import Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_exists_I_eq_of_flat_of_comap_mapOnProdOver_eq_of_isDiscreteValuationRing
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_RelEffCartierDiv_exists_I_eq_ker_and_pullbackAlong_eq_and_saturated_of_isDiscreteValuationRing

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem solution
    {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} [IsProper f]
    {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (g : Spec (CommRingCat.of O) ⟶ S)
    (T' : Type u) [Field T'] [Algebra O T'] [IsFractionRing O T']
    {gT : Spec (CommRingCat.of T') ⟶ S} (hψ : Spec.map (CommRingCat.ofHom (algebraMap O T')) ≫ g = gT)
    {r : ℕ} (E : RelEffCartierDiv f r gT) :
    ∃ Ebar : RelEffCartierDiv f r g,
      Ebar.I = (E.I.subschemeι ≫ mapOnProdOver f (Spec.map (CommRingCat.ofHom (algebraMap O T'))) hψ).ker ∧
      Ebar.pullbackAlong (Spec.map (CommRingCat.ofHom (algebraMap O T'))) hψ = E ∧
      ∀ (ϖ : O), Irreducible ϖ → ∀ (U : (pullback f g).affineOpens) (s : Γ(pullback f g, U)),
        (pullback f g).presheaf.map (homOfLE (le_top : (U : (pullback f g).Opens) ≤ ⊤)).op
            ((pullback.snd f g).appTop ((Scheme.ΓSpecIso (CommRingCat.of O)).inv ϖ)) * s ∈ Ebar.I.ideal U →
          s ∈ Ebar.I.ideal U := by

  obtain ⟨hJE, hsat⟩ :=
    Scheme.IdealSheafData.comap_ker_subschemeIota_comp_mapOnProdOver_eq_and_saturated_of_isDiscreteValuationRing
      g T' hψ E.I

  haveI := AlgebraicGeometry.IdealSheafData.flat_subschemeInclusion_comp_of_forall_mul_mem_of_isDiscreteValuationRing
    (pullback.snd f g) _ hsat

  obtain ⟨Ebar, hI, hpb⟩ :=
    RelEffCartierDiv.exists_I_eq_of_flat_of_comap_mapOnProdOver_eq_of_isDiscreteValuationRing g T' hψ E _ hJE
  refine ⟨Ebar, hI, hpb, ?_⟩
  · intro ϖ hϖ U s hs
    rw [hI] at hs ⊢
    exact hsat ϖ hϖ U s hs
