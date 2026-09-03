import Definitions.Def_LanglandsTunnell_JLConverse
import Definitions.Def_AutomorphicForm_ArchWeightChar
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_RankinSelberg_exists_forall_iwasawaIntegral_eq_const_mul_oneSided_torusPair_add_mirror_of_discreteProfile_conjBlockHarmonic_colHarmonic
attribute [-instance] LanglandsTunnell.CubicInduction.countable_GL2 LanglandsTunnell.CubicInduction.countable_mirabolicIndex M4aHerbrand.isMulCommutative_ideleClassGroup M4aHerbrand.isMulCommutative_sIdeleClassGroup
attribute [-simp] LanglandsTunnell.CubicInduction.upperUnipotent3_zero LanglandsTunnell.CubicInduction.radicalP21_coe LanglandsTunnell.CubicInduction.coe_iotaGL LanglandsTunnell.CubicInduction.radicalP12_coe LanglandsTunnell.CubicInduction.radicalP12_zero LanglandsTunnell.CubicInduction.radicalP21_zero LanglandsTunnell.CubicInduction.upperUnipotent3_coe LanglandsTunnell.CubicLambda.ResolventDatum.s3.injEq LanglandsTunnell.CubicLambda.ResolventDatum.s3.sizeOf_spec LanglandsTunnell.CubicLambda.ResolventDatum.cyclic.sizeOf_spec LanglandsTunnell.CubicLambda.ResolventDatum.cyclic.injEq LanglandsTunnell.RankinSelberg.mem_primeFibre LanglandsTunnell.CubicInduction.longWeyl3_coe LanglandsTunnell.CubicInduction.lowerUnipotent21_coe LanglandsTunnell.CubicInduction.weylPrime3_coe LanglandsTunnell.CubicInduction.gl3AmbientRightTranslate_apply LanglandsTunnell.CubicInduction.CubicInductionForm.mk.injEq LanglandsTunnell.CubicInduction.CubicInductionForm.mk.sizeOf_spec LanglandsTunnell.CubicInduction.coe_diagUnitGL2 LanglandsTunnell.CubicInduction.iotaTorusLocal_zero LanglandsTunnell.CubicInduction.coe_diagUnits2 UnramifiedWhittaker.ProductMeasureData.mk.injEq UnramifiedWhittaker.ProductMeasureData.mk.sizeOf_spec NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent M4aHerbrand.IdeleGaloisDescent.sClassAct_mk M4aHerbrand.SIdeleClassGroup.ofLE_mk M4aHerbrand.repHomOfMulEquivariant_hom_apply M4aHerbrand.coe_finPart_apply M4aHerbrand.SIdeleClassGroup.ofLE_toSIdeleClass M4aHerbrand.IdeleGaloisDescent.sClassAct_toSIdeleClass M4aHerbrand.coe_infPart_apply M4aHerbrand.toSIdeleClass_mk M4aHerbrand.IdeleGaloisDescent.classAct_mk M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq AutomorphicForm.ArchDir.E.sizeOf_spec AutomorphicForm.ArchDir.H.sizeOf_spec
attribute [-simp] AutomorphicForm.ArchDir.Fm.sizeOf_spec LanglandsTunnell.deltaLiftSystem_level LanglandsTunnell.deltaLiftSystem_toRawCentral AutomorphicForm.productionPinsCompact_ν AutomorphicForm.productionPinsCompact_U AutomorphicForm.productionPinsCompact_D AutomorphicForm.productionPinsCompact_nS AutomorphicForm.productionPinsCompact_gen AutomorphicForm.productionPinsCompact_Z AutomorphicForm.productionPinsCompact_mS AutomorphicForm.productionPinsCompact_μ AutomorphicForm.productionPins_nS AutomorphicForm.productionPins_mS AutomorphicForm.productionPins_ν AutomorphicForm.productionPins_Z AutomorphicForm.productionPins_U AutomorphicForm.productionPins_μ AutomorphicForm.productionPins_gen AutomorphicForm.productionPins_D AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one AutomorphicForm.gl2Weyl_val

set_option autoImplicit false

p2m_open "NumberField AutomorphicForm LanglandsTunnell~integral_ofReal_pow_mul_exp_neg_pi_mul_sq_mul_cexp_eq_iteratedDeriv~exists_forall_integrable_oneSided_torusPair_integrand_of_torusBound_of_polyBound~exp_neg_pi_mul_sq_mul_integral_sub_I_mul_pow_mul_exp_eq_iteratedDeriv LanglandsTunnell.Converse~exists_forall_integrable_thetaFree_iwasawaIntegrand_conjBlockPow_colHarmonic_of_oneSided_profile~exists_forall_integrable_xPowGaussian_psi_mul_torusPair_of_oneSided_profile MeasureTheory~setIntegral_iwasawaRegion_eq_two_pi_mul_of_theta_free Set"

theorem LanglandsTunnell.RankinSelberg.exists_forall_iwasawaIntegral_eq_const_mul_oneSided_torusPair_add_mirror_of_discreteProfile_conjBlockHarmonic_colHarmonic
    {P₂ : RealArchParam} (D : ArchDatumR P₂) (k₀ : ℤ)
    (hDW : ∀ (r : rowIsometrySubgroup₀ ℝ) (x : GL (Fin 2) ℝ),
        D.W ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
          (archWeightCharℝ k₀ r : ℂ) * D.W (x : Matrix (Fin 2) (Fin 2) ℝ))
    (a : ℚ) (ha1 : a = -1)
    (u₀ cP uP : ℂ) (a₀ : ZMod 2) (nP m : ℕ) (hm : m = nP + 1) (n : ℕ) (ε' : ℝ)
    (hcol : (ε' = -1 ∧ (n : ℤ) = k₀ - m) ∨ (ε' = 1 ∧ (n : ℤ) = m - k₀))
    (W : ℝ → ℂ)
    (hWpos : ∀ t : ℝ, 0 < t → W t = (2 : ℂ) * (t : ℂ) ^ (uP + (nP : ℂ) / 2 + 1) * (Real.exp (-(2 * Real.pi * t)) : ℂ))
    (hWneg : ∀ t : ℝ, t < 0 → W t = 0)
    :
    ∃ σ₁ : ℝ, ∀ s : ℂ, σ₁ < s.re →
    (∫ p : ℝ × ℝ × ℝ × ℝ in Set.univ ×ˢ (Set.univ ×ˢ (Set.Ioi (0 : ℝ) ×ˢ Set.Ioc (0 : ℝ) (2 * Real.pi))),
        (let x : ℝ := p.1
         let y₁ : ℝ := p.2.1
         let y₂ : ℝ := p.2.2.1
         let θ : ℝ := p.2.2.2
         let g : Matrix (Fin 2) (Fin 2) ℝ :=
           !![y₁ * Real.cos θ + x * y₂ * Real.sin θ, -(y₁ * Real.sin θ) + x * y₂ * Real.cos θ;
              y₂ * Real.sin θ, y₂ * Real.cos θ]
         ArchR.quasiChar (u₀ + 2) a₀ (y₁ * y₂)⁻¹ *
             (((|(y₁ * y₂)⁻¹| ^ 2)⁻¹ : ℝ) : ℂ) *
           ((∫ t : ℝ, W t * D.W (ArchR.diagOne ((a : ℝ) * t) * g) *
               (((|t| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((t ^ 2)⁻¹ : ℝ) : ℂ)) *
            (((((Real.cos θ : ℝ) : ℂ) + Complex.I * ((Real.sin θ : ℝ) : ℂ)) *
                  ((((1 / y₁ - 1 / y₂ : ℝ) : ℂ)) + Complex.I * (((x / y₁ : ℝ) : ℂ)))) ^ m *
              (Real.exp (-(Real.pi * ((1 + x ^ 2) / y₁ ^ 2 + 1 / y₂ ^ 2))) : ℂ) *
              ((|y₁ * y₂| : ℝ) : ℂ) *
              (-Complex.I * (a : ℂ)) ^ n *
              (((y₂ * Real.sin θ : ℝ) : ℂ) + (ε' : ℂ) * Complex.I * ((y₂ * Real.cos θ : ℝ) : ℂ)) ^ n *
              ((1 / 2 : ℂ) *
                ((Real.pi * (a : ℝ) ^ 2 * ((y₂ * Real.sin θ) ^ 2 + (y₂ * Real.cos θ) ^ 2) : ℝ) : ℂ)
                    ^ (-((cP + P₂.centralExponent + 2 * s + n + 1) / 2)) *
                Complex.Gamma ((cP + P₂.centralExponent + 2 * s + n + 1) / 2)))) *
           ((y₂ ^ 2 * (|y₁ * y₂| ^ 4)⁻¹ : ℝ) : ℂ)))
      = (Real.pi : ℂ) * Complex.Gammaℝ (cP + P₂.centralExponent + 2 * s + (n : ℂ) + 1) *
          ((-(ε' : ℂ)) ^ n) * (2 : ℂ) *
        ((-1 : ℂ) ^ (a₀.val) *
          (∫ t in Ioi (0 : ℝ), ∫ y₁ in Iio (0 : ℝ), ∫ y₂ in Ioi (0 : ℝ),
            ((t : ℝ) : ℂ) ^ (s + uP + (m : ℂ) / 2 - 2) * (Real.exp (-(2 * Real.pi * t)) : ℂ) *
              ((|y₁| : ℝ) : ℂ) ^ (-(u₀ + 2)) * ((y₂ : ℝ) : ℂ) ^ (-(cP + 2 * s + u₀ + 1)) *
              (Real.exp (-(Real.pi * ((y₁ ^ 2)⁻¹ + t ^ 2 * y₁ ^ 2 + (y₂ ^ 2)⁻¹))) : ℂ) *
              D.W (ArchR.diagOne (t * |y₁| / y₂)) *
              (∫ z : ℝ, (((y₁⁻¹ - y₂⁻¹ + t * y₁ : ℝ) : ℂ) + Complex.I * (z : ℂ)) ^ m *
                (Real.exp (-(Real.pi * z ^ 2)) : ℂ))) +
         (∫ t in Ioi (0 : ℝ), ∫ y₁ in Iio (0 : ℝ), ∫ y₂ in Ioi (0 : ℝ),
            ((t : ℝ) : ℂ) ^ (s + uP + (m : ℂ) / 2 - 2) * (Real.exp (-(2 * Real.pi * t)) : ℂ) *
              ((|y₁| : ℝ) : ℂ) ^ (-(u₀ + 2)) * ((y₂ : ℝ) : ℂ) ^ (-(cP + 2 * s + u₀ + 1)) *
              (Real.exp (-(Real.pi * ((y₁ ^ 2)⁻¹ + t ^ 2 * y₁ ^ 2 + (y₂ ^ 2)⁻¹))) : ℂ) *
              D.W (ArchR.diagOne (-(t * |y₁| / y₂))) *
              (∫ z : ℝ, (((-y₁⁻¹ - y₂⁻¹ - t * y₁ : ℝ) : ℂ) + Complex.I * (z : ℂ)) ^ m *
                (Real.exp (-(Real.pi * z ^ 2)) : ℂ)))) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_iwasawaIntegral_eq_const_mul_oneSided_torusPair_add_mirror_of_discreteProfile_conjBlockHarmonic_colHarmonic.solution
