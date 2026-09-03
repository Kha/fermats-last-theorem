import Mathlib
import Definitions.Def_DedekindDomain_Completion_BaseChange
import P2M.Util
import P2M.Sol.S_IsDedekindDomain_HeightOneSpectrum_exists_units_prod_tensor_map_iterate_eq_tmul_one_of_finrank_dvd_valuation_norm
attribute [-instance] NumberField.AdelicHaar.locallyCompactSpace_adeleRing NumberField.AdelicHaar.finite_residueField_adicCompletionIntegers NumberField.AdelicHaar.locallyCompactSpace_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_finiteAdeleRing NumberField.AdelicHaar.compactSpace_adicCompletionIntegers NumberField.AdelicHaar.t2Space_finiteAdeleRing NumberField.AdelicHaar.t2Space_matrix_adeleRing NumberField.AdelicHaar.t2Space_adeleRing NumberField.AdelicHaar.fact_isOpen_adicCompletionIntegers NumberField.AdelicHaar.t2Space_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_matrix_adeleRing NumberField.AdelicHaar.t2Space_infiniteAdeleRing NumberField.AdelicHaar.properSpace_adicCompletion
attribute [-simp] NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq AutomorphicForm.whittakerCoefficient_zero AutomorphicForm.CarrierPins.mk.injEq AutomorphicForm.CarrierPins.mk.sizeOf_spec AutomorphicForm.unipotentGL2_zero AutomorphicForm.constantTerm_const AutomorphicForm.constantTerm_zero AutomorphicForm.unipotentGL2_coe NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply LanglandsTunnell.TateLocal.conductorExponentAt_one LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero

set_option autoImplicit false

p2m_open "NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum~exists_unique_extension_algEquiv_adicCompletion_of_isField_tensor~ramificationIdx_eq_one_and_inertiaDeg_dvd_of_baseChange_of_unramified"
open scoped TensorProduct

theorem IsDedekindDomain.HeightOneSpectrum.exists_units_prod_tensor_map_iterate_eq_tmul_one_of_finrank_dvd_valuation_norm
    (K L K' M : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Field K'] [NumberField K']
    [Field M] [NumberField M]
    [Algebra K L] [Algebra K K'] [Algebra K M] [Algebra L M] [Algebra K' M]
    [IsScalarTower K L M] [IsScalarTower K K' M] [IsGalois K L]
    (hdisj : Module.finrank K' M = Module.finrank K L)
    (hcomp : ∀ x : M, x ∈ Algebra.adjoin K' (Set.range (algebraMap L M)))
    (hdeg : (Module.finrank K L).Prime) (hK' : Module.finrank K K' = 2)
    (v : HeightOneSpectrum (𝓞 K))
    (hv : ∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w = v →
      Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w).asIdeal w.asIdeal = 1)
    (w : v.Extension (𝓞 L)) (hw : ∀ w' : v.Extension (𝓞 L), w' = w)
    (𝔳 : v.Extension (𝓞 K')) (h𝔳 : ∀ 𝔳' : v.Extension (𝓞 K'), 𝔳' = 𝔳)
    (θ : w.1.adicCompletion L ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)
    (hθ : orderOf θ = Module.finrank K L)
    (hθfix : ∀ y : w.1.adicCompletion L, θ y = y ↔
      y ∈ Set.range (algebraMap (v.adicCompletion K) (w.1.adicCompletion L)))
    (hfin : Module.finrank (v.adicCompletion K) (w.1.adicCompletion L) = Module.finrank K L)
    (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    (hθσ : ∀ y : L, θ (algebraMap L (w.1.adicCompletion L) y) =
      algebraMap L (w.1.adicCompletion L) (σ y))
    (x : 𝔳.1.adicCompletion K') (hx : x ≠ 0)
    (hdiv : ∃ k : ℤ, Valued.v (Algebra.norm (v.adicCompletion K) x) =
      ((Multiplicative.ofAdd ((Module.finrank K L : ℤ) * k) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) :
    ∃ e : (𝔳.1.adicCompletion K' ⊗[v.adicCompletion K] w.1.adicCompletion L)ˣ,
      ((List.range (Module.finrank K L)).map fun i =>
          (⇑(Algebra.TensorProduct.map (AlgHom.id (v.adicCompletion K) (𝔳.1.adicCompletion K'))
              (θ : w.1.adicCompletion L →ₐ[v.adicCompletion K] w.1.adicCompletion L)))^[i]
            (e : 𝔳.1.adicCompletion K' ⊗[v.adicCompletion K] w.1.adicCompletion L)).prod
        = x ⊗ₜ[v.adicCompletion K] (1 : w.1.adicCompletion L) := by p2m_exact_reverting @_root_.P2MW.S_IsDedekindDomain_HeightOneSpectrum_exists_units_prod_tensor_map_iterate_eq_tmul_one_of_finrank_dvd_valuation_norm.solution
