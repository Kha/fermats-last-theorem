import Mathlib
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_ExtCitation_LocalLevel_FundamentalClass
import Definitions.Def_NumberField_IdeleLocalInvariant
import P2M.Util
import P2M.Sol.S_NumberField_IdeleLocalInv_hasLocalInv_iff_of_forall_map_prG_eq

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory groupCohomology NumberField IsDedekindDomain M4aHerbrand
open scoped NumberField.PlaceDecomp

theorem NumberField.IdeleLocalInv.hasLocalInv_iff_of_forall_map_prG_eq
    (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K] [IsGalois E K]
    (D : IdeleGaloisDescent (𝓞 K) E K)
    [MulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ]
    (hactI : ∀ (g : K ≃ₐ[E] K) (z : (AdeleRing (𝓞 K) K)ˣ), g • z = D.unitsAct g z)
    (x₁ x₂ : groupCohomology (Rep.ofMulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ) 2)
    (hx : ∀ (w : HeightOneSpectrum (𝓞 K))
      (prG : Rep.res (NumberField.PlaceDecomp.decomp E K w).subtype (Rep.ofMulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ) ⟶
        Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K w)) (w.adicCompletion K)ˣ),
      (∀ z : (AdeleRing (𝓞 K) K)ˣ, prG.hom (Additive.ofMul z) = Additive.ofMul (finPart w z)) →
      (groupCohomology.map (NumberField.PlaceDecomp.decomp E K w).subtype prG 2).hom x₁
        = (groupCohomology.map (NumberField.PlaceDecomp.decomp E K w).subtype prG 2).hom x₂)
    (v : HeightOneSpectrum (𝓞 E)) (t : AddCircle (1 : ℚ)) :
    NumberField.IdeleLocalInv.HasLocalInv E K D hactI x₁ v t ↔ NumberField.IdeleLocalInv.HasLocalInv E K D hactI x₂ v t := by p2m_exact_reverting @_root_.P2MW.S_NumberField_IdeleLocalInv_hasLocalInv_iff_of_forall_map_prG_eq.solution
