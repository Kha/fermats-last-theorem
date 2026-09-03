import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_X1DegeneracyPullback
import P2M.Util
import P2M.Sol.S_ModularCurve_JH_pullbackAlongHom_pullbackAlongHom_eq_degeneracyPullbackPair_pullbackAlongHom

set_option autoImplicit false

theorem ModularCurve.JH.pullbackAlongHom_pullbackAlongHom_eq_degeneracyPullbackPair_pullbackAlongHom
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) [NeZero (M / p)]
    (hdeg : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩; ModularCurve.JOne.DegeneracyPullbackInputs (M / p) M p)
    [AlgebraicCurve.HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(ModularCurve.x1FunctionFieldBar M)]
    [AlgebraicCurve.HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(ModularCurve.x1FunctionFieldBar (M / p))]
    [AlgebraicCurve.HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H)]

    (ι : ↥(ModularCurve.xHFunctionFieldBar M H) →ₐ[AlgebraicClosure ℚ] ↥(ModularCurve.x1FunctionFieldBar M))
    (hι : ∀ u, ((ι u : ↥(ModularCurve.x1FunctionFieldBar M)) : LaurentSeries (AlgebraicClosure ℚ)) =
      (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hιint : ι.toRingHom.IsIntegral)
    (hιFI : AlgebraicCurve.FundamentalIdentityAlong (AlgebraicClosure ℚ) ι hιint)
    (ι' : ↥(ModularCurve.xHFunctionFieldBar (M / p) (ModularCurve.infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ]
      ↥(ModularCurve.x1FunctionFieldBar (M / p)))
    (hι' : ∀ u, ((ι' u : ↥(ModularCurve.x1FunctionFieldBar (M / p))) : LaurentSeries (AlgebraicClosure ℚ)) =
      (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hι'int : ι'.toRingHom.IsIntegral)
    (hι'FI : AlgebraicCurve.FundamentalIdentityAlong (AlgebraicClosure ℚ) ι' hι'int)

    (αH βH : ↥(ModularCurve.xHFunctionFieldBar (M / p) (ModularCurve.infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ]
      ↥(ModularCurve.xHFunctionFieldBar M H))
    (hα : ∀ u, ((αH u : ↥(ModularCurve.xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
      (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hβ : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
      ∀ u, ((βH u : ↥(ModularCurve.xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
        ModularCurve.qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hαint : αH.toRingHom.IsIntegral) (hβint : βH.toRingHom.IsIntegral)
    (hαFI : AlgebraicCurve.FundamentalIdentityAlong (AlgebraicClosure ℚ) αH hαint)
    (hβFI : AlgebraicCurve.FundamentalIdentityAlong (AlgebraicClosure ℚ) βH hβint) :
    haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
    (∀ x : ModularCurve.JH (M / p) (ModularCurve.infSubgroup p M H hpM),
      AlgebraicCurve.Pic0.pullbackAlongHom ι hιint hιFI (AlgebraicCurve.Pic0.pullbackAlongHom αH hαint hαFI x) =
        ModularCurve.JOne.degeneracyPullbackPair (M / p) M p 0
          (AlgebraicCurve.Pic0.pullbackAlongHom ι' hι'int hι'FI x)) ∧
    (∀ x : ModularCurve.JH (M / p) (ModularCurve.infSubgroup p M H hpM),
      AlgebraicCurve.Pic0.pullbackAlongHom ι hιint hιFI (AlgebraicCurve.Pic0.pullbackAlongHom βH hβint hβFI x) =
        ModularCurve.JOne.degeneracyPullbackPair (M / p) M p 1
          (AlgebraicCurve.Pic0.pullbackAlongHom ι' hι'int hι'FI x)) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_JH_pullbackAlongHom_pullbackAlongHom_eq_degeneracyPullbackPair_pullbackAlongHom.solution
