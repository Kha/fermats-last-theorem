import Mathlib
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_ExtCitation_LocalLevel_FundamentalClass
import Definitions.Def_NumberField_SUnitsModule
import Definitions.Def_NumberField_IdeleLocalInvariant
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_IsDedekindDomain_FiniteUnitIdelesOutside
import P2M.Util
import P2M.Sol.S_NumberField_IdeleLocalInv_map_eq_zero_of_zsmul_eq_zero_of_map_eq_zero_of_capitulation
attribute [-simp] NumberField.SIdele.fibre_inr NumberField.SIdele.toFinite_hom_apply NumberField.SIdele.fibre_inl NumberField.SIdele.toArch_hom_apply GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply NumberField.SUnits.coe_unitOfValuedEqOne NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory groupCohomology NumberField IsDedekindDomain M4aHerbrand
open M4aHerbrand.GenuineDescent
open scoped NumberField.PlaceDecomp

theorem NumberField.IdeleLocalInv.map_eq_zero_of_zsmul_eq_zero_of_map_eq_zero_of_capitulation
    (E K K'' : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Field K''] [NumberField K'']
    [Algebra E K] [Algebra K K''] [Algebra E K''] [IsScalarTower E K K''] [IsGalois E K] [IsGalois E K'']
    (S : Finset (HeightOneSpectrum (𝓞 E)))

    (D : IdeleGaloisDescent (𝓞 K) E K)
    [MulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ]
    (hactI : ∀ (g : K ≃ₐ[E] K) (x : (AdeleRing (𝓞 K) K)ˣ), g • x = D.unitsAct g x)
    (D'' : IdeleGaloisDescent (𝓞 K'') E K'')
    [MulDistribMulAction (K'' ≃ₐ[E] K'') (AdeleRing (𝓞 K'') K'')ˣ]
    (hactI'' : ∀ (g : K'' ≃ₐ[E] K'') (x : (AdeleRing (𝓞 K'') K'')ˣ), g • x = D''.unitsAct g x)

    (M : Rep ℤ (K ≃ₐ[E] K)) (ι : M ⟶ (Rep.ofMulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ)) (hιinj : Function.Injective ι.hom)
    (hιrange : ∀ w : (AdeleRing (𝓞 K) K)ˣ, (∃ m, ι.hom m = Additive.ofMul w) ↔
      w ∈ principalIdeles (𝓞 K) K ⊔ NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K {w | w.under (𝓞 E) ∈ S})
    (M'' : Rep ℤ (K'' ≃ₐ[E] K'')) (ι'' : M'' ⟶ (Rep.ofMulDistribMulAction (K'' ≃ₐ[E] K'') (AdeleRing (𝓞 K'') K'')ˣ)) (hι''inj : Function.Injective ι''.hom)
    (hι''range : ∀ w : (AdeleRing (𝓞 K'') K'')ˣ, (∃ m, ι''.hom m = Additive.ofMul w) ↔
      w ∈ principalIdeles (𝓞 K'') K'' ⊔ NumberField.AdeleRing.unitIdelesOutside (𝓞 K'') K'' {w | w.under (𝓞 E) ∈ S})

    (B : Rep.res (AlgEquiv.restrictNormalHom K : (K'' ≃ₐ[E] K'') →* (K ≃ₐ[E] K)) M ⟶ M'')
    (hB : ∀ m, Additive.toMul (ι''.hom (B.hom m)) = Units.map (genuineBaseChange K K'').β.toMonoidHom (Additive.toMul (ι.hom m)))

    (p : ℕ) [Fact p.Prime]
    (hcap : ∀ (I : Ideal (𝓞 K)) (k : ℕ) (a : 𝓞 K), a ≠ 0 → I ^ p ^ k = Ideal.span {a} →
      (I.map (algebraMap (𝓞 K) (𝓞 K''))).IsPrincipal)

    (u : groupCohomology M 2) (k : ℕ) (hu : (p ^ k : ℤ) • u = 0)
    (hdie : (groupCohomology.map (MonoidHom.id (K ≃ₐ[E] K)) ι 2).hom u = 0) :
    (groupCohomology.map (AlgEquiv.restrictNormalHom K : (K'' ≃ₐ[E] K'') →* (K ≃ₐ[E] K)) B 2).hom u = 0 := by p2m_exact_reverting @_root_.P2MW.S_NumberField_IdeleLocalInv_map_eq_zero_of_zsmul_eq_zero_of_map_eq_zero_of_capitulation.solution
