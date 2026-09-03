import Definitions.Def_AutomorphicForm_CuspidalConstituent
import P2M.Util
import P2M.Sol.S_AutomorphicForm_CuspidalConstituent_mem_span_rightTranslate_sup_span_rightConv_spherical_of_mem_span_cyclic_of_mem_archCutSubmodule_ofChar

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent

theorem AutomorphicForm.CuspidalConstituent.mem_span_rightTranslate_sup_span_rightConv_spherical_of_mem_span_cyclic_of_mem_archCutSubmodule_ofChar
    (F : Type) [Field F] [NumberField F]
    (χ : ∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion →* ℂˣ)
    (Ψ₁ φ : AdelicGL2 (𝓞 F) F → ℂ) (hΨ₁ : Continuous Ψ₁)
    (hχ₁ : Ψ₁ ∈ archCutSubmodule F (ArchTypeFamily.ofChar F χ))
    (hχφ : φ ∈ archCutSubmodule F (ArchTypeFamily.ofChar F χ))
    (hφ : φ ∈ Submodule.span ℂ
      {ψ | ∃ g ∈ finiteAdelicGL2Subgroup F, ∃ k ∈ (⨆ w : InfinitePlace F, (rowIsometryInclAt₀ F w).range),
        ψ = rightTranslate F (g * k) Ψ₁ ∨
        ∃ (f : AdelicGL2 (𝓞 F) F → ℂ) (tys : ArchTypeFamily F), IsFactorizableTestFn F f ∧ IsArchBiFinite F tys f ∧
          ψ = rightTranslate F (g * k) (rightConv F Ψ₁ f)}) :
    φ ∈ Submodule.span ℂ ((fun g => rightTranslate F g Ψ₁) '' (finiteAdelicGL2Subgroup F : Set (AdelicGL2 (𝓞 F) F))) ⊔
      Submodule.span ℂ
        {ψ | ∃ g ∈ finiteAdelicGL2Subgroup F,
          ∃ (fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ) (ff : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) → ℂ),
            IsArchTestFactor F fa ∧ IsArchFactorBiFinite F (ArchTypeFamily.ofChar F χ) fa ∧
            (∀ (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion) (x : GL (Fin 2) (InfiniteAdeleRing F)),
              fa (archRowIsometryInclAt₀ F w k * x * (archRowIsometryInclAt₀ F w k)⁻¹) = fa x) ∧
            IsFinTestFactor F ff ∧
            ψ = rightTranslate F g (rightConv F Ψ₁
              (fun y => fa (AdelicLevel.glArch (𝓞 F) F y) * ff (AdelicLevel.glFin (𝓞 F) F y)))} := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_CuspidalConstituent_mem_span_rightTranslate_sup_span_rightConv_spherical_of_mem_span_cyclic_of_mem_archCutSubmodule_ofChar.solution
