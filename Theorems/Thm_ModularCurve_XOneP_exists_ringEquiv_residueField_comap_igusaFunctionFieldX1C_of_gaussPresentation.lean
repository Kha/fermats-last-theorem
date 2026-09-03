import Mathlib
import Definitions.Def_ModularCurve_IgusaFunctionFieldX1
import P2M.Util
import P2M.Sol.S_ModularCurve_XOneP_exists_ringEquiv_residueField_comap_igusaFunctionFieldX1C_of_gaussPresentation

set_option autoImplicit false

theorem ModularCurve.XOneP.exists_ringEquiv_residueField_comap_igusaFunctionFieldX1C_of_gaussPresentation
    (L : Type) [Field L] (K : IntermediateField L (LaurentSeries L))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (W₀ : ValuationSubring ↥K)
    (hW₀ : ∀ f : ↥K, f ∈ W₀ ↔ ∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧
      (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)))
    (hnu : ∀ (f : ↥K) (x y : PowerSeries A), y.map (IsLocalRing.residue A) ≠ 0 →
      (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)) →
      (f ∈ W₀.nonunits ↔ x.map (IsLocalRing.residue A) = 0))
    (hA : ∀ a : A, algebraMap A ↥K a ∈ W₀)
    (M : ℕ) (w : ModularCurve.IntegralWeightOneForm (IsLocalRing.ResidueField A) M)
    (hmem : ∀ (f : ↥K) (x y : PowerSeries A), y.map (IsLocalRing.residue A) ≠ 0 →
      (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)) →
      HahnSeries.ofPowerSeries ℤ (IsLocalRing.ResidueField A) (x.map (IsLocalRing.residue A)) /
          HahnSeries.ofPowerSeries ℤ (IsLocalRing.ResidueField A) (y.map (IsLocalRing.residue A))
        ∈ ModularCurve.igusaFunctionFieldX1C (IsLocalRing.ResidueField A) M w)
    (hsurj : ∀ z : LaurentSeries (IsLocalRing.ResidueField A),
      z ∈ ModularCurve.igusaFunctionFieldX1C (IsLocalRing.ResidueField A) M w →
      ∃ (f : ↥K) (x y : PowerSeries A), y.map (IsLocalRing.residue A) ≠ 0 ∧
        (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
          = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)) ∧
        HahnSeries.ofPowerSeries ℤ (IsLocalRing.ResidueField A) (x.map (IsLocalRing.residue A)) /
          HahnSeries.ofPowerSeries ℤ (IsLocalRing.ResidueField A) (y.map (IsLocalRing.residue A)) = z)
    (σ : ↥K ≃ₐ[L] ↥K) (hσA : ∀ a : A, σ (algebraMap A ↥K a) = algebraMap A ↥K a)

    (hA₁ : ∀ a : A, algebraMap A ↥K a ∈ W₀.comap (σ : ↥K ≃ₐ[L] ↥K).toAlgHom.toRingHom) :
    ∃ θ : IsLocalRing.ResidueField ↥(W₀.comap (σ : ↥K ≃ₐ[L] ↥K).toAlgHom.toRingHom) ≃+*
        ↥(ModularCurve.igusaFunctionFieldX1C (IsLocalRing.ResidueField A) M w),
      (∀ (f : ↥(W₀.comap (σ : ↥K ≃ₐ[L] ↥K).toAlgHom.toRingHom)) (x y : PowerSeries A), y.map (IsLocalRing.residue A) ≠ 0 →
        ((σ (f : ↥K) : ↥K) : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
          = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)) →
        ((θ (IsLocalRing.residue _ f) : ↥(ModularCurve.igusaFunctionFieldX1C (IsLocalRing.ResidueField A) M w)) :
            LaurentSeries (IsLocalRing.ResidueField A))
          = HahnSeries.ofPowerSeries ℤ (IsLocalRing.ResidueField A) (x.map (IsLocalRing.residue A)) /
            HahnSeries.ofPowerSeries ℤ (IsLocalRing.ResidueField A) (y.map (IsLocalRing.residue A))) ∧
      (∀ a : A, θ (IsLocalRing.residue _ ⟨algebraMap A ↥K a, hA₁ a⟩) =
        algebraMap (IsLocalRing.ResidueField A) ↥(ModularCurve.igusaFunctionFieldX1C (IsLocalRing.ResidueField A) M w)
          (IsLocalRing.residue A a)) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_XOneP_exists_ringEquiv_residueField_comap_igusaFunctionFieldX1C_of_gaussPresentation.solution
