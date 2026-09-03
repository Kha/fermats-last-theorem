import Definitions.Def_LanglandsTunnell_CubicInduction_SlabL2Cusp
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_SlabL2_continuousLinearMap_eq_of_forall_toL2_eq

set_option autoImplicit false

open Matrix IsDedekindDomain NumberField AutomorphicForm MeasureTheory

theorem LanglandsTunnell.CubicInduction.SlabL2.continuousLinearMap_eq_of_forall_toL2_eq
    (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (a b : ℝ) (Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ))
    {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [T2Space E]
    (T T' : ↥(cuspidalSubspace ω a b Φ₀) →L[ℂ] E)
    (_h : ∀ (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hF : F ∈ cuspFunctions ω a b Φ₀),
      T ⟨toL2 ω a b Φ₀ ⟨F, hF.1⟩, toL2_mem_cuspidalSubspace_of_mem_cuspFunctions ω a b Φ₀ hF⟩ =
        T' ⟨toL2 ω a b Φ₀ ⟨F, hF.1⟩, toL2_mem_cuspidalSubspace_of_mem_cuspFunctions ω a b Φ₀ hF⟩) :
    T = T' := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_continuousLinearMap_eq_of_forall_toL2_eq.solution
