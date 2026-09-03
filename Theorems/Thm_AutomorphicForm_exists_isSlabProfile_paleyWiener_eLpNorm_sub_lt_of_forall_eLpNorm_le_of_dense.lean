import Definitions.Def_AutomorphicForm_AutomorphicFnAt
import Definitions.Def_AutomorphicForm_SlabProfile
import Definitions.Def_AutomorphicForm_ResidualSpan
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_RationalTorusUnipotentQuotient
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_CarrierPins
import Mathlib.Analysis.Meromorphic.NormalForm
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_isSlabProfile_paleyWiener_eLpNorm_sub_lt_of_forall_eLpNorm_le_of_dense

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm
open scoped NNReal ENNReal Topology

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel

noncomputable section

theorem AutomorphicForm.exists_isSlabProfile_paleyWiener_eLpNorm_sub_lt_of_forall_eLpNorm_le_of_dense
    (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
      (d₁ d₂ : ℝ) (_hd₁ : 0 < d₁) (_hd : d₁ < d₂)
      (Φ : Set (AdelicGL2 (𝓞 F) F))
      (ξ : (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).Z →* ℂˣ)
      (_hξ : Continuous ξ) (_hξu : ∀ z, ‖((ξ z : ℂˣ) : ℂ)‖ = 1)
      (φ : AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ : AutomorphicForm.IsSlabProfile F (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).Z ξ φ)
      (a b : ℝ) (_ha : 0 < a)
      (_hband : ∀ g : AdelicGL2 (𝓞 F) F, φ g ≠ 0 → NumberField.AdelicHeight.adelicHeight F g ∈ Set.Icc a b)
      (T : Type) [MeasurableSpace T] (ρ : MeasureTheory.Measure T) (ev : T → AdelicGL2 (𝓞 F) F)
      (κ : ℝ≥0∞) (_hκ : κ ≠ ∞)
      (_hL2 : ∀ ψ : AdelicGL2 (𝓞 F) F → ℂ,
        AutomorphicForm.IsSlabProfile F (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).Z ξ ψ →
        eLpNorm (fun q : AutomorphicForm.RationalTorusUnipotentQuotient F => φ q.out - ψ q.out) 2
            ((AutomorphicForm.rationalTorusUnipotentQuotientMeasure F).restrict
              {q | NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det q.out) ∈ Set.Icc d₁ d₂}) ≤
          κ * eLpNorm (fun τ : T => φ (ev τ) - ψ (ev τ)) 2 ρ)
      (E : Set (AdelicGL2 (𝓞 F) F → ℂ))
      (_hPW : ∀ (n : ℕ) (e : Fin n → AdelicGL2 (𝓞 F) F → ℂ), (∀ i, e i ∈ E) →
    ∃ (ι : Type) (_ : Fintype ι) (μ ν : ι → ((AdeleRing (𝓞 F) F)ˣ →* ℂˣ)) (r : ι → ι)
          (ψf : ι → ℂ → AdelicGL2 (𝓞 F) F → ℂ) (ψ : AdelicGL2 (𝓞 F) F → ℂ),
          (∀ e, IsUnitaryChar (𝓞 F) F (μ e)) ∧ (∀ e, IsUnitaryChar (𝓞 F) F (ν e)) ∧
          (∀ e, IsIdeleClassChar (𝓞 F) F (μ e)) ∧ (∀ e, IsIdeleClassChar (𝓞 F) F (ν e)) ∧
          (∀ e, Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((μ e x : ℂˣ) : ℂ)) ∧
          (∀ e, Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((ν e x : ℂˣ) : ℂ)) ∧
          (∀ (e : ι) (z : (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).Z),
            μ e (z : (AdeleRing (𝓞 F) F)ˣ) * ν e (z : (AdeleRing (𝓞 F) F)ˣ) = ξ z) ∧
          (∀ e, μ (r e) = ν e ∧ ν (r e) = μ e) ∧
          (∀ e e' : ι, e ≠ e' → ∃ x ∈ NumberField.TateGlobal.normOneIdeles F,
            μ e x ≠ μ e' x ∨ ν e x ≠ ν e' x) ∧
          (∀ e s, IsInducedSection (𝓞 F) F (etaFst (μ e) α hα s) (etaSnd (ν e) α hα s) (ψf e s)) ∧
          (∀ e, Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => ψf e p.1 p.2)) ∧
          (∀ e g, Differentiable ℂ (fun s => ψf e s g)) ∧
          (∀ e s, IsArchKFinite F (ψf e s)) ∧ (∀ e s, IsKfSmooth F (ψf e s)) ∧
          (∀ (e : ι) (w : InfinitePlace F), ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup F w) → ℂ),
            FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 F) F),
              (fun k : ↥(archRowIsometrySubgroup F w) => ψf e s (g * (k : AdelicGL2 (𝓞 F) F))) ∈ W) ∧
          (∀ (e : ι) (n : ℕ) (σ₀ : ℝ) (C : Set (AdelicGL2 (𝓞 F) F)), IsCompact C →
            ∃ m : ℝ → ℝ, Integrable m ∧ (∃ B : ℝ, ∀ t, m t ≤ B) ∧ ∀ σ' : ℝ, |σ'| ≤ σ₀ →
              ∀ (t : ℝ), ∀ g ∈ C, (1 + |t|) ^ n * ‖ψf e ((σ' : ℂ) + (t : ℂ) * Complex.I) g‖ ≤ m t) ∧
          AutomorphicForm.IsSlabProfile F (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).Z ξ ψ ∧
          (∀ (σ' : ℝ) (g : AdelicGL2 (𝓞 F) F),
            ψ g = ∑ e, (((4 * Real.pi)⁻¹ : ℝ) : ℂ) * ∫ t : ℝ, ψf e ((σ' : ℂ) + (t : ℂ) * Complex.I) g) ∧
          (∀ g : AdelicGL2 (𝓞 F) F, ψ g ≠ 0 → NumberField.AdelicHeight.adelicHeight F g ∈ Set.Icc a b) ∧
          (ψ = fun g => ∑ i, e i g))
      (_hdense : ∀ δ > (0 : ℝ), ∃ (n : ℕ) (e : Fin n → AdelicGL2 (𝓞 F) F → ℂ), (∀ i, e i ∈ E) ∧
        eLpNorm (fun τ : T => φ (ev τ) - ∑ i, e i (ev τ)) 2 ρ < ENNReal.ofReal δ),
    ∃ a' b' : ℝ, 0 < a' ∧ (∀ g : AdelicGL2 (𝓞 F) F, φ g ≠ 0 → NumberField.AdelicHeight.adelicHeight F g ∈ Set.Icc a' b') ∧
    ∀ ε > (0 : ℝ),
    ∃ (ι : Type) (_ : Fintype ι) (μ ν : ι → ((AdeleRing (𝓞 F) F)ˣ →* ℂˣ)) (r : ι → ι)
      (ψf : ι → ℂ → AdelicGL2 (𝓞 F) F → ℂ) (ψ : AdelicGL2 (𝓞 F) F → ℂ),
      (∀ e, IsUnitaryChar (𝓞 F) F (μ e)) ∧ (∀ e, IsUnitaryChar (𝓞 F) F (ν e)) ∧
      (∀ e, IsIdeleClassChar (𝓞 F) F (μ e)) ∧ (∀ e, IsIdeleClassChar (𝓞 F) F (ν e)) ∧
      (∀ e, Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((μ e x : ℂˣ) : ℂ)) ∧
      (∀ e, Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((ν e x : ℂˣ) : ℂ)) ∧
      (∀ (e : ι) (z : (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).Z),
        μ e (z : (AdeleRing (𝓞 F) F)ˣ) * ν e (z : (AdeleRing (𝓞 F) F)ˣ) = ξ z) ∧
      (∀ e, μ (r e) = ν e ∧ ν (r e) = μ e) ∧
      (∀ e e' : ι, e ≠ e' → ∃ x ∈ NumberField.TateGlobal.normOneIdeles F,
        μ e x ≠ μ e' x ∨ ν e x ≠ ν e' x) ∧
      (∀ e s, IsInducedSection (𝓞 F) F (etaFst (μ e) α hα s) (etaSnd (ν e) α hα s) (ψf e s)) ∧
      (∀ e, Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => ψf e p.1 p.2)) ∧
      (∀ e g, Differentiable ℂ (fun s => ψf e s g)) ∧
      (∀ e s, IsArchKFinite F (ψf e s)) ∧ (∀ e s, IsKfSmooth F (ψf e s)) ∧
      (∀ (e : ι) (w : InfinitePlace F), ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup F w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 F) F),
          (fun k : ↥(archRowIsometrySubgroup F w) => ψf e s (g * (k : AdelicGL2 (𝓞 F) F))) ∈ W) ∧
      (∀ (e : ι) (n : ℕ) (σ₀ : ℝ) (C : Set (AdelicGL2 (𝓞 F) F)), IsCompact C →
        ∃ m : ℝ → ℝ, Integrable m ∧ (∃ B : ℝ, ∀ t, m t ≤ B) ∧ ∀ σ' : ℝ, |σ'| ≤ σ₀ →
          ∀ (t : ℝ), ∀ g ∈ C, (1 + |t|) ^ n * ‖ψf e ((σ' : ℂ) + (t : ℂ) * Complex.I) g‖ ≤ m t) ∧
      AutomorphicForm.IsSlabProfile F (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).Z ξ ψ ∧
      (∀ (σ' : ℝ) (g : AdelicGL2 (𝓞 F) F),
        ψ g = ∑ e, (((4 * Real.pi)⁻¹ : ℝ) : ℂ) * ∫ t : ℝ, ψf e ((σ' : ℂ) + (t : ℂ) * Complex.I) g) ∧
      (∀ g : AdelicGL2 (𝓞 F) F, ψ g ≠ 0 → NumberField.AdelicHeight.adelicHeight F g ∈ Set.Icc a' b') ∧
      eLpNorm (fun q : AutomorphicForm.RationalTorusUnipotentQuotient F => φ q.out - ψ q.out) 2
        ((AutomorphicForm.rationalTorusUnipotentQuotientMeasure F).restrict
          {q | NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det q.out) ∈ Set.Icc d₁ d₂}) <
        ENNReal.ofReal ε := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_isSlabProfile_paleyWiener_eLpNorm_sub_lt_of_forall_eLpNorm_le_of_dense.solution
