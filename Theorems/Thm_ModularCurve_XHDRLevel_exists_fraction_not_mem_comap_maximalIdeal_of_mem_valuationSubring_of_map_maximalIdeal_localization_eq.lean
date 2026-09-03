import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import P2M.Util
import P2M.Sol.S_ModularCurve_XHDRLevel_exists_fraction_not_mem_comap_maximalIdeal_of_mem_valuationSubring_of_map_maximalIdeal_localization_eq

set_option autoImplicit false

open scoped MatrixGroups TensorProduct
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra IsLocalRing AlgebraicCurve ModularCurve ModularCurve.XHDRLevel
  ModularCurve.JZeroNeronObjectAtP

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.XHDRLevel.exists_fraction_not_mem_comap_maximalIdeal_of_mem_valuationSubring_of_map_maximalIdeal_localization_eq
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    [Algebra (R p) ↥A] (halg : algebraMap (R p) ↥A = ρ)
    (B : Type) [CommRing B] [Algebra (R p) B] [Algebra.FiniteType (R p) B] [Module.Flat (R p) B]
    (W : ValuationSubring ↥(xHFunctionFieldBar M H))
    (γ : (↥A ⊗[R p] B) →+* ↥(xHFunctionFieldBar M H)) (hγG : ∀ t, γ t ∈ W)
    (hγinj : Function.Injective γ)
    (hγfrac : ∀ e : ↥(xHFunctionFieldBar M H), ∃ a s : (↥A ⊗[R p] B), s ≠ 0 ∧ e * γ s = γ a)
    (hγA : ∀ a : ↥A, γ (Algebra.TensorProduct.includeLeftRingHom a) = algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (a : AlgebraicClosure ℚ))
    (hWA : ∀ a : ↥A, algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (a : AlgebraicClosure ℚ) ∈ W)
    (hW𝔪 : ∀ a : ↥A, (⟨algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (a : AlgebraicClosure ℚ), hWA a⟩ : ↥W) ∈ IsLocalRing.maximalIdeal ↥W ↔
      a ∈ IsLocalRing.maximalIdeal ↥A)
    (hpW : (algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (p : AlgebraicClosure ℚ)) ∈ W.nonunits)
    (𝔯₀ : Ideal (↥A ⊗[R p] B)) (h𝔯₀def : ∀ t, t ∈ 𝔯₀ ↔ (⟨γ t, hγG t⟩ : ↥W) ∈ IsLocalRing.maximalIdeal ↥W)
    [h𝔯₀ : 𝔯₀.IsPrime]
    (hmin : (IsLocalRing.maximalIdeal ↥A).map ((algebraMap (↥A ⊗[R p] B) (Localization.AtPrime 𝔯₀)).comp
        (Algebra.TensorProduct.includeLeft (R := R p) (S := R p) (A := ↥A) (B := B)).toRingHom) =
      IsLocalRing.maximalIdeal (Localization.AtPrime 𝔯₀))
    (h : ↥(xHFunctionFieldBar M H)) (hh : h ∈ W) :
    ∃ a c : (↥A ⊗[R p] B), c ∉ 𝔯₀ ∧ h * γ c = γ a := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_XHDRLevel_exists_fraction_not_mem_comap_maximalIdeal_of_mem_valuationSubring_of_map_maximalIdeal_localization_eq.solution
