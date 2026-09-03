import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_BorelSubgroup
import Definitions.Def_NumberField_TateGlobalZeta
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_eq_sum_prod_archComponent_of_isArchKFinite

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.TateGlobal
open AutomorphicForm AutomorphicForm.WindowedSiegel IsDedekindDomain

theorem AutomorphicForm.exists_eq_sum_prod_archComponent_of_isArchKFinite
    (F : Type) [Field F] [NumberField F]
    (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (_hμc : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((μ x : ℂˣ) : ℂ))
    (_hνc : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((ν x : ℂˣ) : ℂ))
    (U : AdelicGL2 (𝓞 F) F → ℂ) (_hUc : Continuous U) (_hUK : IsArchKFinite F U)
    (_hUB : ∀ (b : AdelicGL2 (𝓞 F) F) (hb : b ∈ adelicBorel (𝓞 F) F),
        glFin (𝓞 F) F b = 1 →
        (∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F b))) →
        ∀ g : AdelicGL2 (𝓞 F) F,
          U (b * g) = ((μ (borelDiagFst (⟨b, hb⟩ : ↥(adelicBorel (𝓞 F) F))) : ℂˣ) : ℂ)
            * ((ν (borelDiagSnd (⟨b, hb⟩ : ↥(adelicBorel (𝓞 F) F))) : ℂˣ) : ℂ) * U g) :
    ∃ (m : ℕ) (f : Fin m → (w : InfinitePlace F) → GL (Fin 2) w.Completion → ℂ),
      (∀ j w, Continuous (f j w)) ∧
      (∀ j w, RightTranslatesSpanFinite (rowIsometrySubgroup w.Completion) (f j w)) ∧
      (∀ (j : Fin m) (w : InfinitePlace F) (b : GL (Fin 2) w.Completion) (hb : b ∈ borelSubgroup w.Completion),
        IsRowIsometry b → ∀ g : GL (Fin 2) w.Completion, IsRowIsometry g →
          f j w (b * g) = ((archLocalChar μ w (borelDiagFst (⟨b, hb⟩ : ↥(borelSubgroup w.Completion))) : ℂˣ) : ℂ)
            * ((archLocalChar ν w (borelDiagSnd (⟨b, hb⟩ : ↥(borelSubgroup w.Completion))) : ℂˣ) : ℂ)
            * f j w g) ∧
      ∀ k : AdelicGL2 (𝓞 F) F, k ∈ adelicMaximalCompact F → glFin (𝓞 F) F k = 1 →
        U k = ∑ j, ∏ w, f j w (archComponent F w (glArch (𝓞 F) F k)) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_eq_sum_prod_archComponent_of_isArchKFinite.solution
