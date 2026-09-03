import Mathlib
import Definitions.Def_ModularCurve_LaurentCoeff
import P2M.Util
import P2M.Sol.S_ModularCurve_valuationSubring_eq_of_comap_eq_of_forall_exists_coeffMap_eq
set_option autoImplicit false
open IsLocalRing ModularCurve

theorem ModularCurve.valuationSubring_eq_of_comap_eq_of_forall_exists_coeffMap_eq (p : ℕ) [Fact p.Prime]
    (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((p : ℕ) : O)})
    (ιO : O →+* AlgebraicClosure ℚ)
    {A : ValuationSubring (AlgebraicClosure ℚ)} {k : Type*} [Field k] [CharP k p] (red : A →+* k)
    (hιA : ∀ a : O, ιO a ∈ A)
    {F : Type*} [Field F] {L : Type*} [Field L] (θO : O →+* L) (θF : F →+* L)
    (hgen : Subfield.closure (Set.range θF ∪ Set.range θO) = ⊤)
    (𝒱 𝒲 : ValuationSubring L) (hpL : ((p : ℕ) : L) ≠ 0)
    (hp𝒱 : ((p : ℕ) : L) ∈ 𝒱.nonunits) (hp𝒲 : ((p : ℕ) : L) ∈ 𝒲.nonunits)
    (hdisc : ∀ g ∈ 𝒱, g ≠ 0 → ∃ n : ℕ, ∃ u ∈ 𝒱, u⁻¹ ∈ 𝒱 ∧ g = ((p : ℕ) : L) ^ n * u)
    (hO𝒱 : ∀ a, θO a ∈ 𝒱) (hO𝒲 : ∀ a, θO a ∈ 𝒲)
    (htr : 𝒱.comap θF = 𝒲.comap θF)
    (hpt : ((p : ℕ) : F) ∈ (𝒱.comap θF).nonunits)
    (hdivt : ∀ f ∈ (𝒱.comap θF).nonunits, f * ((p : ℕ) : F)⁻¹ ∈ 𝒱.comap θF)
    (ρ : ↥𝒲 →+* LaurentSeries k)
    (hker : ∀ g : ↥𝒲, ρ g = 0 ↔ (g : L) ∈ 𝒲.nonunits)
    (hρO : ∀ a, ρ ⟨θO a, hO𝒲 a⟩ = HahnSeries.C (red ⟨ιO a, hιA a⟩))
    (hρF : ∀ (f : F) (h : θF f ∈ 𝒲), ∃ y : LaurentSeries (ZMod p),
      coeffMap (ZMod.castHom (dvd_refl p) k) y = ρ ⟨θF f, h⟩) :
    𝒱 = 𝒲 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_valuationSubring_eq_of_comap_eq_of_forall_exists_coeffMap_eq.solution
