import Definitions.Def_AutomorphicForm_GodementSection
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_BorelSubgroup
import Definitions.Def_LanglandsTunnell_TateLocalZeta
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_sum_mul_prod_localZeta_bottomRow_eq_of_isArchKFinite

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicFourier NumberField.AdelicLevel NumberField.TateGlobal
open AutomorphicForm AutomorphicForm.WindowedSiegel IsDedekindDomain
open scoped NNReal SchwartzMap

open scoped Classical in

theorem AutomorphicForm.exists_sum_mul_prod_localZeta_bottomRow_eq_of_isArchKFinite
    (F : Type) [Field F] [NumberField F]
    [∀ w : InfinitePlace F, MeasurableSpace w.Completion] [∀ w : InfinitePlace F, BorelSpace w.Completion]
    (μa : (w : InfinitePlace F) → Measure w.Completion) [∀ w, (μa w).IsAddHaarMeasure]
    (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (_hμ : IsUnitaryChar (𝓞 F) F μ) (_hν : IsUnitaryChar (𝓞 F) F ν)
    (_hμc : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((μ x : ℂˣ) : ℂ))
    (_hνc : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((ν x : ℂˣ) : ℂ))
    (U : AdelicGL2 (𝓞 F) F → ℂ) (_hUc : Continuous U) (_hUK : IsArchKFinite F U)
    (_hUB : ∀ (b : AdelicGL2 (𝓞 F) F) (hb : b ∈ adelicBorel (𝓞 F) F),
        glFin (𝓞 F) F b = 1 →
        (∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F b))) →
        ∀ g : AdelicGL2 (𝓞 F) F,
          U (b * g) = ((μ (borelDiagFst (⟨b, hb⟩ : ↥(adelicBorel (𝓞 F) F))) : ℂˣ) : ℂ)
            * ((ν (borelDiagSnd (⟨b, hb⟩ : ↥(adelicBorel (𝓞 F) F))) : ℂˣ) : ℂ) * U g) :
    ∃ (m : ℕ) (g : Fin m → 𝓢((Fin 2 → mixedEmbedding.mixedSpace F), ℂ))
      (Φa : Fin m → (w : InfinitePlace F) → (Fin 2 → w.Completion) → ℂ)
      (E : Fin m → ℂ → ℂ),
      (∀ j, Differentiable ℂ (E j)) ∧
      (∀ j (y : Fin 2 → InfiniteAdeleRing F),
        g j (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (y i)) = ∏ w, Φa j w (fun i => y i w)) ∧
      ∀ (z : ℂ), 0 < z.re →
        ∀ (k : AdelicGL2 (𝓞 F) F), k ∈ adelicMaximalCompact F → glFin (𝓞 F) F k = 1 →
          (∑ j, E j z * (((μ (Matrix.GeneralLinearGroup.det k) : ℂˣ) : ℂ)
              * ∏ w, LanglandsTunnell.TateLocal.localZeta (μa w)
                  (fun t => Φa j w (fun i => t
                    * (archComponent F w (glArch (𝓞 F) F k) : Matrix (Fin 2) (Fin 2) w.Completion) 1 i))
                  (archLocalChar (μ * ν⁻¹) w) z))
            = U k := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_sum_mul_prod_localZeta_bottomRow_eq_of_isArchKFinite.solution
