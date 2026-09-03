import Definitions.Def_AutomorphicForm_FnTwist
import Definitions.Def_AutomorphicForm_GaussTwist
import Definitions.Def_AutomorphicForm_BoundedGenuineCuspRealization
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_fnTwist_gaussSumFn_isSmoothCuspData
open NumberField AutomorphicForm

theorem LanglandsTunnell.fnTwist_gaussSumFn_isSmoothCuspData
    (F : Type) [Field F] [NumberField F]
    (η : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (hηF : IsIdeleClassChar (𝓞 F) F η) (hcont : Continuous η)
    (hη₁ : IsUnitaryChar (𝓞 F) F η)
    (𝔣 : Ideal (𝓞 F)) (h𝔣 : 𝔣 ≠ ⊥) (hmod : HeckeCharacter.AdmitsModulus F η 𝔣)
    {nS : MeasurableSpace (AdeleRing (𝓞 F) F)} (ν : MeasureTheory.Measure (AdeleRing (𝓞 F) F))
    {Z : Subgroup (AdeleRing (𝓞 F) F)ˣ} {ξ : Z →* ℂˣ}
    (pins : CarrierPins F) (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsLsXiFunction (𝓞 F) F Z ξ φ)
    (hint : ∀ g, MeasureTheory.Integrable (constantTermIntegrand unipotentGL2 φ g) ν)
    (hcusp : @IsCuspidalFn _ nS _ _ ν unipotentGL2 φ)
    (hkf : IsKfSmooth F φ)
    (hgen : IsBoundedGenuineFn F pins ψ φ) :
    Continuous (chiDet (𝓞 F) F η) ∧
      IsLsXiFunction (𝓞 F) F Z (twistedCentralChar F Z ξ η)
        (fnTwist F η (AutomorphicForm.GaussTwist.gaussSumFn F η 𝔣 φ)) ∧
      (@IsCuspidalFn _ nS _ _ ν unipotentGL2
        (fnTwist F η (AutomorphicForm.GaussTwist.gaussSumFn F η 𝔣 φ))) ∧
      IsKfSmooth F (fnTwist F η (AutomorphicForm.GaussTwist.gaussSumFn F η 𝔣 φ)) ∧
      (∀ (z : (AdeleRing (𝓞 F) F)ˣ) (b : ℂ),
        (∀ g : AdelicGL2 (𝓞 F) F, φ (centralScalar (𝓞 F) F z * g) = b * φ g) →
        ∀ g : AdelicGL2 (𝓞 F) F,
          fnTwist F η (AutomorphicForm.GaussTwist.gaussSumFn F η 𝔣 φ) (centralScalar (𝓞 F) F z * g)
            = ((η z : ℂˣ) : ℂ) ^ 2 * b *
                fnTwist F η (AutomorphicForm.GaussTwist.gaussSumFn F η 𝔣 φ) g) ∧
      IsBoundedGenuineFn F pins ψ (fnTwist F η (AutomorphicForm.GaussTwist.gaussSumFn F η 𝔣 φ)) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_fnTwist_gaussSumFn_isSmoothCuspData.solution
