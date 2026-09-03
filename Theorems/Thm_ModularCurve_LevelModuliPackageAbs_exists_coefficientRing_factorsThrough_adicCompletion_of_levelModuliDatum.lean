import Mathlib
import Definitions.Def_ModularCurve_LevelModuliPackage
import Definitions.Def_ModularCurve_LevelModuliPackageAbs
import P2M.Util
import P2M.Sol.S_ModularCurve_LevelModuliPackageAbs_exists_coefficientRing_factorsThrough_adicCompletion_of_levelModuliDatum
attribute [-instance] AdicCompletion.instIsLocalRingMaximalIdeal
attribute [-simp] MvPowerSeries.kw_coeff_pderiv FormalGroup.nthSeries_zero FormalGroup.evalNSMul_zero FormalGroup.DrinfeldLevel.mk.sizeOf_spec FormalGroup.DrinfeldLevel.mk.injEq

set_option autoImplicit false

open ModularCurve IsLocalRing

theorem ModularCurve.LevelModuliPackageAbs.exists_coefficientRing_factorsThrough_adicCompletion_of_levelModuliDatum
    (q : ℕ) [Fact q.Prime]

    (A₀ : Type) [CommRing A₀] [IsDomain A₀] [IsDiscreteValuationRing A₀]
    (hA₀q : maximalIdeal A₀ = Ideal.span {(q : A₀)}) [Finite (ResidueField A₀)]

    {D : LevelModuliDatum.{0} A₀} (P₀ : LevelModuliPackageAbs A₀ D) [Algebra.FiniteType A₀ P₀.B₀]
    (𝔪 : Ideal P₀.B₀) [𝔪.IsMaximal] (hq𝔪 : algebraMap A₀ P₀.B₀ (q : A₀) ∈ 𝔪) :
    letI : Field (P₀.B₀ ⧸ 𝔪) := Ideal.Quotient.field 𝔪
    ∃ (_ : IsLocalRing (AdicCompletion 𝔪 P₀.B₀)) (_ : IsNoetherianRing (AdicCompletion 𝔪 P₀.B₀))
      (_ : IsAdicComplete (maximalIdeal (AdicCompletion 𝔪 P₀.B₀)) (AdicCompletion 𝔪 P₀.B₀))
      (_ : IsScalarTower A₀ P₀.B₀ (AdicCompletion 𝔪 P₀.B₀))
      (resR : AdicCompletion 𝔪 P₀.B₀ →+* P₀.B₀ ⧸ 𝔪) (_ : Function.Surjective resR)
      (_ : RingHom.ker resR = maximalIdeal (AdicCompletion 𝔪 P₀.B₀))
      (_ : resR.comp (algebraMap P₀.B₀ (AdicCompletion 𝔪 P₀.B₀)) = Ideal.Quotient.mk 𝔪)
      (W₀ : Type) (_ : CommRing W₀) (_ : IsDomain W₀) (_ : IsDiscreteValuationRing W₀)
      (_ : IsAdicComplete (maximalIdeal W₀) W₀) (_ : maximalIdeal W₀ = Ideal.span {(q : W₀)})
      (res₀ : W₀ →+* P₀.B₀ ⧸ 𝔪) (_ : Function.Surjective res₀) (_ : RingHom.ker res₀ = maximalIdeal W₀)
      (_ : Algebra W₀ (AdicCompletion 𝔪 P₀.B₀)) (_ : Algebra A₀ W₀) (_ : IsScalarTower A₀ W₀ (AdicCompletion 𝔪 P₀.B₀))
      (_ : ∀ w : W₀, resR (algebraMap W₀ (AdicCompletion 𝔪 P₀.B₀) w) = res₀ w),
      CharP (P₀.B₀ ⧸ 𝔪) q ∧
      ∀ (T : Type) [CommRing T] [IsLocalRing T] [IsArtinianRing T] [Algebra W₀ T]
        [Algebra A₀ T] [IsScalarTower A₀ W₀ T]
        (resT : T →+* P₀.B₀ ⧸ 𝔪), Function.Surjective resT → RingHom.ker resT = maximalIdeal T →
        (∀ w : W₀, resT (algebraMap W₀ T w) = res₀ w) →
        ∀ φ : P₀.B₀ →ₐ[A₀] T, (∀ b : P₀.B₀, resT (φ b) = resR (algebraMap P₀.B₀ (AdicCompletion 𝔪 P₀.B₀) b)) →
          ∃! Φ : AdicCompletion 𝔪 P₀.B₀ →ₐ[W₀] T,
            (∀ r : AdicCompletion 𝔪 P₀.B₀, resT (Φ r) = resR r) ∧
            ∀ b : P₀.B₀, Φ (algebraMap P₀.B₀ (AdicCompletion 𝔪 P₀.B₀) b) = φ b := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_LevelModuliPackageAbs_exists_coefficientRing_factorsThrough_adicCompletion_of_levelModuliDatum.solution
