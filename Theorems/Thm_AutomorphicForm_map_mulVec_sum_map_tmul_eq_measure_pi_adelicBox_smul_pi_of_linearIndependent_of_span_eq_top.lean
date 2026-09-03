import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_NumberField_AdelicBox
import P2M.Util
import P2M.Sol.S_AutomorphicForm_map_mulVec_sum_map_tmul_eq_measure_pi_adelicBox_smul_pi_of_linearIndependent_of_span_eq_top
attribute [-instance] instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions
attribute [-simp] ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicBox IsDedekindDomain
open scoped TensorProduct

theorem AutomorphicForm.map_mulVec_sum_map_tmul_eq_measure_pi_adelicBox_smul_pi_of_linearIndependent_of_span_eq_top
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (ι : Type) [Fintype ι] (b : ι → Matrix (Fin 2) (Fin 2) L) (v : Fin 2 → L)
    (hli : LinearIndependent K fun i => (b i).mulVec v)
    (hsp : Submodule.span K (Set.range fun i => (b i).mulVec v) = ⊤)
    [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)]
    [MeasurableSpace (AdeleRing (𝓞 L) L)] [BorelSpace (AdeleRing (𝓞 L) L)]
    (ρ : Measure (ι → AdeleRing (𝓞 K) K)) [ρ.IsAddHaarMeasure]
    (μ₁ : Measure (AdeleRing (𝓞 L) L)) [μ₁.IsAddHaarMeasure] (hμ₁ : μ₁ (adelicBox L) = 1) :
    ρ {a | ∀ i, a i ∈ adelicBox K} ≠ 0 ∧ ρ {a | ∀ i, a i ∈ adelicBox K} ≠ ⊤ ∧
    Measure.map (fun a : ι → AdeleRing (𝓞 K) K =>
        ((∑ i, (b i).map fun l : L => l ⊗ₜ[K] a i).map
            (((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans
              (M4aHerbrand.Bridge.genuineRingEquiv K L)).toRingHom)).mulVec
          fun j => algebraMap L (AdeleRing (𝓞 L) L) (v j)) ρ =
      ρ {a | ∀ i, a i ∈ adelicBox K} • Measure.pi fun _ : Fin 2 => μ₁ := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_map_mulVec_sum_map_tmul_eq_measure_pi_adelicBox_smul_pi_of_linearIndependent_of_span_eq_top.solution
