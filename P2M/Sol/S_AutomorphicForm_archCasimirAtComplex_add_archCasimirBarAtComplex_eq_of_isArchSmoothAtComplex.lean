import Definitions.Def_AutomorphicForm_ArchDerivCasimirComplex
import Definitions.Def_AutomorphicForm_ArchDerivCasimirComplexAPI
import Theorems.Thm_AutomorphicForm_archDerivAtComplex_commutator_of_isArchSmoothAtComplex
import P2M.Util
namespace P2MW.S_AutomorphicForm_archCasimirAtComplex_add_archCasimirBarAtComplex_eq_of_isArchSmoothAtComplex

set_option autoImplicit false

open NumberField AutomorphicForm NumberField.InfinitePlace NumberField.InfinitePlace.Completion

theorem solution
    (F : Type) [Field F] [NumberField F] {w : InfinitePlace F} (hw : w.IsComplex)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : IsArchSmoothAtComplex hw φ) :
    archCasimirAtComplex hw φ + archCasimirBarAtComplex hw φ
      = (1 / 8 : ℂ) • archKCasimirAtComplex hw φ
        - (1 / 8 : ℂ) • (archDerivAtComplex hw .H (archDerivAtComplex hw .H φ) +
            (archDerivAtComplex hw .E (archDerivAtComplex hw .E φ + archDerivAtComplex hw .Fm φ) +
              archDerivAtComplex hw .Fm (archDerivAtComplex hw .E φ + archDerivAtComplex hw .Fm φ)) +
            (archDerivAtComplex hw .iFm (archDerivAtComplex hw .iFm φ - archDerivAtComplex hw .iE φ) -
              archDerivAtComplex hw .iE (archDerivAtComplex hw .iFm φ - archDerivAtComplex hw .iE φ))) := by
  obtain ⟨-, -, hEF, -, -, -, -, -, -, -, -, hiEiF, -, -, -⟩ :=
    archDerivAtComplex_commutator_of_isArchSmoothAtComplex F hw φ hφ
  have hs : ∀ d : ArchDirComplex, IsArchSmoothAtComplex hw (archDerivAtComplex hw d φ) :=
    fun d => hφ.archDerivAtComplex d
  have hsc : ∀ (c : ℂ) (d : ArchDirComplex), IsArchSmoothAtComplex hw (c • archDerivAtComplex hw d φ) :=
    fun c d => (hs d).smul c
  have Dsub : ∀ (X : ArchDirComplex) (u v : AdelicGL2 (𝓞 F) F → ℂ),
      IsArchSmoothAtComplex hw u → IsArchSmoothAtComplex hw v →
      archDerivAtComplex hw X (u - v) = archDerivAtComplex hw X u - archDerivAtComplex hw X v := by
    intro X u v hu hv
    rw [sub_eq_add_neg, ← neg_one_smul ℂ v, archDerivAtComplex_add hu (hv.smul _), archDerivAtComplex_smul,
      neg_one_smul, ← sub_eq_add_neg]
  simp only [archCasimirAtComplex, archCasimirBarAtComplex, archKCasimirAtComplex, archDelAt, archDelBarAt,
    ArchDir.toComplex, ArchDir.toComplexI, archDerivAtComplex_smul,
    archDerivAtComplex_add (hs _) (hs _), archDerivAtComplex_add (hs _) (hsc _ _),
    Dsub _ _ _ (hs _) (hs _), Dsub _ _ _ (hs _) (hsc _ _)]
  funext g
  have h3 := congrFun hEF g
  have h12 := congrFun hiEiF g
  simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul] at h3 h12 ⊢
  linear_combination (-(1 / 4) : ℂ) * h3 + (1 / 4 : ℂ) * h12
    + (-(1 / 8 : ℂ) * archDerivAtComplex hw .iH (archDerivAtComplex hw .iH φ) g
        - (1 / 2 : ℂ) * archDerivAtComplex hw .iE (archDerivAtComplex hw .iFm φ) g) * Complex.I_sq
