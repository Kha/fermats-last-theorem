import Definitions.Def_AutomorphicForm_CuspidalConstituent
import P2M.Util
import P2M.Sol.S_AutomorphicForm_CuspidalConstituent_continuous_and_mem_archCutSubmodule_ofChar_of_eq_integral_rightTranslate_adelicArchGLIncl

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent

theorem AutomorphicForm.CuspidalConstituent.continuous_and_mem_archCutSubmodule_ofChar_of_eq_integral_rightTranslate_adelicArchGLIncl
    (F : Type) [Field F] [NumberField F]
    (χ : ∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion →* ℂˣ)
    (hχ : ∀ w : InfinitePlace F, Continuous fun k : rowIsometrySubgroup₀ w.Completion => ((χ w k : ℂˣ) : ℂ))
    [MeasurableSpace (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion)]
    [BorelSpace (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion)]
    (μ : Measure (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion))
    [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant]
    (ι : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) →* GL (Fin 2) (InfiniteAdeleRing F))
    (hι : ∀ (κ : ∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) (w : InfinitePlace F),
      archComponent F w (ι κ) = ((κ w : rowIsometrySubgroup₀ w.Completion) : GL (Fin 2) w.Completion))
    (P : (AdelicGL2 (𝓞 F) F → ℂ) → (AdelicGL2 (𝓞 F) F → ℂ))
    (hP : ∀ (φ : AdelicGL2 (𝓞 F) F → ℂ) (x : AdelicGL2 (𝓞 F) F),
      P φ x = ∫ κ, (∏ w, ((χ w (κ w)⁻¹ : ℂˣ) : ℂ)) * φ (x * adelicArchGLIncl F (ι κ)) ∂μ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : Continuous φ) :
    Continuous (P φ) ∧
    P φ ∈ archCutSubmodule F (ArchTypeFamily.ofChar F χ) ∧
    (φ ∈ archCutSubmodule F (ArchTypeFamily.ofChar F χ) → P φ = φ) ∧
    (∀ g : AdelicGL2 (𝓞 F) F, (∀ κ, g * adelicArchGLIncl F (ι κ) = adelicArchGLIncl F (ι κ) * g) →
      P (rightTranslate F g φ) = rightTranslate F g (P φ)) ∧
    (∀ κ : ∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion,
      P (rightTranslate F (adelicArchGLIncl F (ι κ)) φ) = (∏ w, ((χ w (κ w) : ℂˣ) : ℂ)) • P φ) ∧
    (∀ ψ : AdelicGL2 (𝓞 F) F → ℂ, Continuous ψ → P (φ + ψ) = P φ + P ψ) ∧
    (∀ c : ℂ, P (c • φ) = c • P φ) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_CuspidalConstituent_continuous_and_mem_archCutSubmodule_ofChar_of_eq_integral_rightTranslate_adelicArchGLIncl.solution
