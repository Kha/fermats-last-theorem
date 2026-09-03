import Mathlib
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_ModularCurve_ShimuraKernel
import P2M.Util
import P2M.Sol.S_ModularCurve_heckeBetaHBar_pins_and_smul_pullbackAlongHom_of_qExpand_pins

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open AlgebraicCurve ModularCurve

theorem ModularCurve.heckeBetaHBar_pins_and_smul_pullbackAlongHom_of_qExpand_pins
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) [NeZero (M / p)]
    (hβN : ModularCurve.HeckeBetaHDefined (M / p) (ModularCurve.infSubgroup p M H hpM) p)
    [AlgebraicCurve.HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H)]
    (ι : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
            (ModularCurve.xHTopFunctionFieldC ℚ (M / p) (ModularCurve.infSubgroup p M H hpM) (M / p * p))) →ₐ[AlgebraicClosure ℚ]
        ↥(ModularCurve.xHFunctionFieldBar M H))
    (hιcoe : ∀ u : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
            (ModularCurve.xHTopFunctionFieldC ℚ (M / p) (ModularCurve.infSubgroup p M H hpM) (M / p * p))),
      ((ι u : ↥(ModularCurve.xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hι : ι.toRingHom.IsIntegral) (hFIι : AlgebraicCurve.FundamentalIdentityAlong (AlgebraicClosure ℚ) ι hι)
    (hιs : Function.Surjective ι)
    (pb : (ZMod (M / p))ˣ) (hpb : ((pb : (ZMod (M / p))ˣ) : ZMod (M / p)) = (p : ZMod (M / p)))
    (θ : ↥(ModularCurve.xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(ModularCurve.xHFunctionFieldBar M H))
    (hθ : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
      ∀ (f : ↥(xHFunctionFieldBar M H)) (u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))), (f : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)) →
        ((θ f : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hθ₂ : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
    ∀ (c : (ZMod (M / p))ˣ), (c : ZMod (M / p)) = (p : ZMod (M / p)) →
      ∀ (f : ↥(xHFunctionFieldBar M H)) (u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))), (f : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)) →
        ((θ f : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = ((diamondAutHBar (M / p) (infSubgroup p M H hpM) c u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) : LaurentSeries (AlgebraicClosure ℚ))) :
    let ιe : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
            (ModularCurve.xHTopFunctionFieldC ℚ (M / p) (ModularCurve.infSubgroup p M H hpM) (M / p * p))) ≃ₐ[AlgebraicClosure ℚ]
        ↥(ModularCurve.xHFunctionFieldBar M H) := AlgEquiv.ofBijective ι ⟨ι.toRingHom.injective, hιs⟩
    let W := (ιe.trans θ.symm).trans ιe.symm
    (∀ x : ↥(ModularCurve.xHFunctionFieldBar (M / p) (ModularCurve.infSubgroup p M H hpM)),
        W (ModularCurve.heckeBetaHBar (AlgebraicClosure ℚ) (M / p) (ModularCurve.infSubgroup p M H hpM) p x) =
          ModularCurve.heckeAlphaHBar (AlgebraicClosure ℚ) (M / p) (ModularCurve.infSubgroup p M H hpM) p x) ∧
    (∀ x : ↥(ModularCurve.xHFunctionFieldBar (M / p) (ModularCurve.infSubgroup p M H hpM)),
        W (ModularCurve.heckeAlphaHBar (AlgebraicClosure ℚ) (M / p) (ModularCurve.infSubgroup p M H hpM) p x) =
          ModularCurve.heckeBetaHBar (AlgebraicClosure ℚ) (M / p) (ModularCurve.infSubgroup p M H hpM) p
            ((ModularCurve.diamondAutHBar (M / p) (ModularCurve.infSubgroup p M H hpM) pb).symm x)) ∧
    (∀ x₁ : Pic0 (AlgebraicClosure ℚ)
        ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
          (ModularCurve.xHTopFunctionFieldC ℚ (M / p) (ModularCurve.infSubgroup p M H hpM) (M / p * p))),
      SemilinearAut.ofAlgAut θ • Pic0.pullbackAlongHom ι hι hFIι x₁ =
        Pic0.pullbackAlongHom ι hι hFIι (SemilinearAut.ofAlgAut W.symm • x₁)) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_heckeBetaHBar_pins_and_smul_pullbackAlongHom_of_qExpand_pins.solution
