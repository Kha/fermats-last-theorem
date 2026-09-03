import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_AutomorphicForm_SlabProfile
import Definitions.Def_NumberField_AdelicHaar
import P2M.Util
import P2M.Sol.S_AutomorphicForm_isSlabProfile_and_forall_eq_sum_integral_of_paleyWiener_packet
attribute [-instance] HeckePair.instSMulCommClassSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instAlgebraSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instOneSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instIsScalarTowerSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instRingSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instMulSubtypeForallMemSubmoduleHeckeAlgebra FixedPoints.instMulActionElemFixedPointsOfSMulCommClass_definitions FixedPoints.module FixedPoints.instSMulElemFixedPointsOfSMulCommClass_definitions FixedPoints.instAddCommMonoidElemFixedPoints_definitions instCountableOfNumberField_definitions
attribute [-simp] LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one HeckePair.convTerm_mk HeckePair.coe_apply_add HeckePair.coe_apply_smul FixedPoints.coe_zero FixedPoints.coe_smul FixedPoints.coe_add LocalGL2.swapUnit_val

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicHaar AutomorphicForm
open IsDedekindDomain
open scoped ComplexConjugate NNReal ENNReal ContDiff

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.isSlabProfile_and_forall_eq_sum_integral_of_paleyWiener_packet
    (K : Type) [Field K] [NumberField K] :
    let αm : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits
    letI := adeleBorel (𝓞 K) K
    ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ))
      (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
      (ιP : Type) [Fintype ιP] (n : ιP → ℕ)
      (μP νP : ιP → ((AdeleRing (𝓞 K) K)ˣ →* ℂˣ))
      (_hμ : ∀ i, IsUnitaryChar (𝓞 K) K (μP i)) (_hν : ∀ i, IsUnitaryChar (𝓞 K) K (νP i))
      (_hμic : ∀ i, IsIdeleClassChar (𝓞 K) K (μP i)) (_hνic : ∀ i, IsIdeleClassChar (𝓞 K) K (νP i))
      (_hμν : ∀ (i : ιP) (z : (AdeleRing (𝓞 K) K)ˣ), μP i z * νP i z = ξ ⟨z, Subgroup.mem_top z⟩)
      (φP : ∀ i : ιP, Fin (n i) → ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hφP : ∀ i j s, IsInducedSection (𝓞 K) K (etaFst (μP i) αm hαm s) (etaSnd (νP i) αm hαm s) (φP i j s))
      (_hφPjc : ∀ i j, Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => φP i j p.1 p.2))
      (_hφPhol : ∀ i j (g : AdelicGL2 (𝓞 K) K), Differentiable ℂ (fun s => φP i j s g))
      (_hφPflat : ∀ i j (s : ℂ) (k : adelicMaximalCompact K),
        φP i j s (k : AdelicGL2 (𝓞 K) K) = φP i j 0 (k : AdelicGL2 (𝓞 K) K))
      (h : ∀ i : ιP, Fin (n i) → ℝ → ℂ)
      (_hh : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (h i j)) (_hhc : ∀ i j, HasCompactSupport (h i j)),
    let c : ∀ i : ιP, Fin (n i) → ℂ → ℂ := fun i j s => ∫ u : ℝ, h i j u * Complex.exp (s * (u : ℂ))
    let ψf : ιP → ℂ → AdelicGL2 (𝓞 K) K → ℂ := fun i s g => ∑ j, c i j s * φP i j s g
    let ψ : AdelicGL2 (𝓞 K) K → ℂ := fun g =>
      ∑ i, (((4 * Real.pi)⁻¹ : ℝ) : ℂ) * ∫ t : ℝ, ψf i ((t : ℂ) * Complex.I) g
    AutomorphicForm.IsSlabProfile K (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) ξ ψ ∧
    (∀ (σ' : ℝ) (g : AdelicGL2 (𝓞 K) K),
      ψ g = ∑ i, (((4 * Real.pi)⁻¹ : ℝ) : ℂ) * ∫ t : ℝ, ψf i ((σ' : ℂ) + (t : ℂ) * Complex.I) g) ∧
    (∀ (i : ιP) (nn : ℕ) (σ₀ : ℝ) (C : Set (AdelicGL2 (𝓞 K) K)), IsCompact C →
      ∃ m : ℝ → ℝ, Integrable m ∧ (∃ B : ℝ, ∀ t, m t ≤ B) ∧ ∀ σ' : ℝ, |σ'| ≤ σ₀ →
        ∀ (t : ℝ), ∀ g ∈ C, (1 + |t|) ^ nn * ‖ψf i ((σ' : ℂ) + (t : ℂ) * Complex.I) g‖ ≤ m t) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_isSlabProfile_and_forall_eq_sum_integral_of_paleyWiener_packet.solution
