import Mathlib
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_ExtCitation_LocalLevel_FundamentalClass
import Definitions.Def_NumberField_SUnitsModule
import Definitions.Def_NumberField_IdeleLocalInvariant
import P2M.Util
import P2M.Sol.S_NumberField_IdeleLocalInv_exists_zsmul_eq_zero_and_map_eq_of_map_pi_eq_zero

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 400000
p2m_open "CategoryTheory groupCohomology~exists_map_eq_of_map_eq_zero_of_injective_of_surjective NumberField IsDedekindDomain M4aHerbrand"
open scoped NumberField.PlaceDecomp

theorem NumberField.IdeleLocalInv.exists_zsmul_eq_zero_and_map_eq_of_map_pi_eq_zero
    (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K] [IsGalois E K]

    (D : IdeleGaloisDescent (𝓞 K) E K)
    [MulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ]
    (hactI : ∀ (g : K ≃ₐ[E] K) (x : (AdeleRing (𝓞 K) K)ˣ), g • x = D.unitsAct g x)
    [MulDistribMulAction (K ≃ₐ[E] K) (IdeleClassGroup (𝓞 K) K)]
    (hact : ∀ (g : K ≃ₐ[E] K) (c : IdeleClassGroup (𝓞 K) K), g • c = D.classAct g c)

    [MulDistribMulAction (K ≃ₐ[E] K) Kˣ]
    (hactF : ∀ (g : (K ≃ₐ[E] K)) (a : Kˣ), ((g • a : Kˣ) : K) = g (a : K))
    (j : (Rep.ofMulDistribMulAction (K ≃ₐ[E] K) Kˣ) ⟶ (Rep.ofMulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ))
    (hj : ∀ a : Kˣ, j.hom (Additive.ofMul a) = Additive.ofMul (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) a))
    (π : Rep.ofMulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ ⟶ Rep.ofMulDistribMulAction (K ≃ₐ[E] K) (IdeleClassGroup (𝓞 K) K))
    (hπ : ∀ y : (AdeleRing (𝓞 K) K)ˣ, π.hom (Additive.ofMul y) = Additive.ofMul (QuotientGroup.mk y : IdeleClassGroup (𝓞 K) K))
    (p : ℕ) [Fact p.Prime]
    (x : groupCohomology (Rep.ofMulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ) 2) (k : ℕ) (hx : (p ^ k : ℤ) • x = 0)
    (hπx : (groupCohomology.map (MonoidHom.id (K ≃ₐ[E] K)) π 2).hom x = 0) :
    ∃ (y : groupCohomology (Rep.ofMulDistribMulAction (K ≃ₐ[E] K) Kˣ) 2) (k' : ℕ), (p ^ k' : ℤ) • y = 0 ∧
      (groupCohomology.map (MonoidHom.id (K ≃ₐ[E] K)) j 2).hom y = x := by p2m_exact_reverting @_root_.P2MW.S_NumberField_IdeleLocalInv_exists_zsmul_eq_zero_and_map_eq_of_map_pi_eq_zero.solution
