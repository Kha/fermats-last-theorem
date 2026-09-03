import Definitions.Def_AutomorphicForm_WeylSelectors
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_EtaFamily
import P2M.Util
import P2M.Sol.S_AutomorphicForm_WeylIntegrable_norm_apply_weyl_unipotent_le_uniform

set_option autoImplicit false

theorem AutomorphicForm.WeylIntegrable.norm_apply_weyl_unipotent_le_uniform (F : Type) [Field F] [NumberField F]
    (α : (NumberField.AdeleRing (NumberField.RingOfIntegers F) F)ˣ →* ℝˣ) (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
    (μ ν : (NumberField.AdeleRing (NumberField.RingOfIntegers F) F)ˣ →* ℂˣ) (s : ℂ)
    (φ : AdelicGL2 (NumberField.RingOfIntegers F) F → ℂ)
    (hμ : IsUnitaryChar (NumberField.RingOfIntegers F) F μ) (hν : IsUnitaryChar (NumberField.RingOfIntegers F) F ν)
    (hφ : IsInducedSection (NumberField.RingOfIntegers F) F (etaFst μ α hα s) (etaSnd ν α hα s) φ)
    (hφc : Continuous φ) {K : Set (AdelicGL2 (NumberField.RingOfIntegers F) F)} (hK : IsCompact K) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ g ∈ K, ∀ u : NumberField.AdeleRing (NumberField.RingOfIntegers F) F,
      ‖φ ((adelicWeyl (NumberField.RingOfIntegers F) F)⁻¹ * unipotentGL2 u * g)‖ ≤
        B * ((α (yUnit (selRel F u.1 u.2)) : ℝˣ) : ℝ) ^ (-(2 * s.re + 1)) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_WeylIntegrable_norm_apply_weyl_unipotent_le_uniform.solution
