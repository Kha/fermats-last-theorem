import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_AutomorphicForm_LocalWeightedOrbital
import P2M.Util
import P2M.Sol.S_AutomorphicForm_integral_twistedConj_map_algEquiv_mul_weight_eq_integral_unipotentGL2_of_biInvariant
attribute [-simp] LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open LanglandsTunnell.CubicInduction (diagUnits2)

theorem AutomorphicForm.integral_twistedConj_map_algEquiv_mul_weight_eq_integral_unipotentGL2_of_biInvariant
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) (w : v.Extension (𝓞 L))
    (hw : Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w.1).asIdeal w.1.asIdeal = 1)
    (θ : w.1.adicCompletion L ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)
    (hθ : orderOf θ = Module.finrank (v.adicCompletion K) (w.1.adicCompletion L))
    (a b : (v.adicCompletion K)ˣ) (hab : a ≠ b)
    (α β : (w.1.adicCompletion L)ˣ)
    (hT : AutomorphicForm.sigmaCentralizer (Matrix.GeneralLinearGroup.map θ.toAlgHom.toRingHom) (diagUnits2 α β) =
      (AutomorphicForm.localCentralizer K v (diagUnits2 a b)).map
        (Matrix.GeneralLinearGroup.map (algebraMap (v.adicCompletion K) (w.1.adicCompletion L))))
    (τ' : @Measure (AutomorphicForm.sigmaCentralizer
        (Matrix.GeneralLinearGroup.map θ.toAlgHom.toRingHom) (diagUnits2 α β)) (borel _))
    (hτ' : @Measure.IsHaarMeasure _ _ _ (borel _) τ')
    (hτ'1 : τ' {t | (t : GL (Fin 2) (w.1.adicCompletion L)) ∈ AutomorphicForm.localIntegralSet L w.1} = 1)

    (Φ : GL (Fin 2) (w.1.adicCompletion L) → ℂ) (hΦ : AutomorphicForm.IsLocalTestFn L w.1 Φ)
    (hΦK : ∀ g k₁ k₂ : GL (Fin 2) (w.1.adicCompletion L),
      k₁ ∈ AutomorphicForm.localIntegralSet L w.1 → k₂ ∈ AutomorphicForm.localIntegralSet L w.1 →
        Φ (k₁ * g * k₂) = Φ g)

    (s : GL (Fin 2) (w.1.adicCompletion L) → ℝ) (hs0 : ∀ x, 0 ≤ s x)
    (hsm : Measurable[AutomorphicForm.localGLBorel L w.1] s) (hsc : HasCompactSupport s)
    (hs1 : ∀ x : GL (Fin 2) (w.1.adicCompletion L),
      Φ (x⁻¹ * diagUnits2 α β * Matrix.GeneralLinearGroup.map θ.toAlgHom.toRingHom x) ≠ 0 →
        ∫ t : AutomorphicForm.sigmaCentralizer (Matrix.GeneralLinearGroup.map θ.toAlgHom.toRingHom)
            (diagUnits2 α β), s ((t : GL (Fin 2) (w.1.adicCompletion L)) * x) ∂τ' = 1)

    [MeasurableSpace (w.1.adicCompletion L)] [BorelSpace (w.1.adicCompletion L)]
    (μE : Measure (w.1.adicCompletion L)) [μE.IsAddHaarMeasure]
    (hμE : μE (w.1.adicCompletionIntegers L : Set (w.1.adicCompletion L)) = 1) :
    ∫ x : GL (Fin 2) (w.1.adicCompletion L),
        Φ (x⁻¹ * diagUnits2 α β * Matrix.GeneralLinearGroup.map θ.toAlgHom.toRingHom x) *
          ((AutomorphicForm.LocalWeight.weight x : ℝ) : ℂ) * (s x : ℂ)
      ∂(AutomorphicForm.localHaar L w.1) =
      ∫ y : w.1.adicCompletion L,
        Φ (diagUnits2 α β *
            AutomorphicForm.unipotentGL2
              (θ y - ((β * α⁻¹ : (w.1.adicCompletion L)ˣ) : w.1.adicCompletion L) * y)) *
          ((2 * Real.log (max 1 ‖y‖) : ℝ) : ℂ) ∂μE := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_integral_twistedConj_map_algEquiv_mul_weight_eq_integral_unipotentGL2_of_biInvariant.solution
