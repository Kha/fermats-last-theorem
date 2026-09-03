import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_AutomorphicForm_ArchDerivCasimirComplex
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_RightConvolution
import P2M.Util
import P2M.Sol.S_AutomorphicForm_isFactorizableTestFn_leftCasimirComplex_and_rightConv_mem_of_isArchBiFinite

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain
open AutomorphicForm.CuspidalConstituent

theorem AutomorphicForm.isFactorizableTestFn_leftCasimirComplex_and_rightConv_mem_of_isArchBiFinite
    (K : Type) [Field K] [NumberField K]
    (D : Set (AdelicGL2 (𝓞 K) K))
    (w : InfinitePlace K) (hw : w.IsComplex)
    (N : Ideal (𝓞 K)) (tys : AutomorphicForm.ArchTypeFamily K)
    (α : AdelicGL2 (𝓞 K) K → ℂ) (hαf : IsFactorizableTestFn K α) (hαb : IsArchBiFinite K tys α)
    (hαU : ∀ g : AdelicGL2 (𝓞 K) K, ∀ k ∈ (levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K), α (k * g) = α g ∧ α (g * k) = α g) :
    let L : ArchDirComplex → (AdelicGL2 (𝓞 K) K → ℂ) → (AdelicGL2 (𝓞 K) K → ℂ) :=
      fun d γ y => deriv (fun t : ℝ => γ (archFlowAtComplex hw d (-t) * y)) 0
    let β : AdelicGL2 (𝓞 K) K → ℂ := fun y =>
      -((1 / 4 : ℂ) * ((1 / 4 : ℂ) * ((1 : ℂ) * L .H (L .H (α)) y + ((-Complex.I) : ℂ) * L .H (L .iH (α)) y + ((-Complex.I) : ℂ) * L .iH (L .H (α)) y + (-1 : ℂ) * L .iH (L .iH (α)) y)) - (1 / 2 : ℂ) * ((1 / 2 : ℂ) * ((1 : ℂ) * L .H (α) y + ((-Complex.I) : ℂ) * L .iH (α) y)) + (1 / 4 : ℂ) * ((1 : ℂ) * L .E (L .Fm (α)) y + ((-Complex.I) : ℂ) * L .E (L .iFm (α)) y + ((-Complex.I) : ℂ) * L .iE (L .Fm (α)) y + (-1 : ℂ) * L .iE (L .iFm (α)) y))
    let βb : AdelicGL2 (𝓞 K) K → ℂ := fun y =>
      -((1 / 4 : ℂ) * ((1 / 4 : ℂ) * ((1 : ℂ) * L .H (L .H (α)) y + (Complex.I : ℂ) * L .H (L .iH (α)) y + (Complex.I : ℂ) * L .iH (L .H (α)) y + (-1 : ℂ) * L .iH (L .iH (α)) y)) - (1 / 2 : ℂ) * ((1 / 2 : ℂ) * ((1 : ℂ) * L .H (α) y + (Complex.I : ℂ) * L .iH (α) y)) + (1 / 4 : ℂ) * ((1 : ℂ) * L .E (L .Fm (α)) y + (Complex.I : ℂ) * L .E (L .iFm (α)) y + (Complex.I : ℂ) * L .iE (L .Fm (α)) y + (-1 : ℂ) * L .iE (L .iFm (α)) y))
    (IsFactorizableTestFn K β ∧ IsArchBiFinite K tys β ∧ IsFactorizableTestFn K βb ∧ IsArchBiFinite K tys βb) ∧
    (∀ (l : List ArchDirComplex), IsFactorizableTestFn K (l.foldr L α)) ∧
    (∀ x' : AdelicGL2 (𝓞 K) K → ℂ, Continuous x' →
      (rightConv K x' β = fun g =>
        -((1 / 4 : ℂ) * ((1 / 4 : ℂ) * ((1 : ℂ) * rightConv K x' (L .H (L .H (α))) g + ((-Complex.I) : ℂ) * rightConv K x' (L .H (L .iH (α))) g + ((-Complex.I) : ℂ) * rightConv K x' (L .iH (L .H (α))) g + (-1 : ℂ) * rightConv K x' (L .iH (L .iH (α))) g)) - (1 / 2 : ℂ) * ((1 / 2 : ℂ) * ((1 : ℂ) * rightConv K x' (L .H (α)) g + ((-Complex.I) : ℂ) * rightConv K x' (L .iH (α)) g)) + (1 / 4 : ℂ) * ((1 : ℂ) * rightConv K x' (L .E (L .Fm (α))) g + ((-Complex.I) : ℂ) * rightConv K x' (L .E (L .iFm (α))) g + ((-Complex.I) : ℂ) * rightConv K x' (L .iE (L .Fm (α))) g + (-1 : ℂ) * rightConv K x' (L .iE (L .iFm (α))) g))) ∧
      (rightConv K x' βb = fun g =>
        -((1 / 4 : ℂ) * ((1 / 4 : ℂ) * ((1 : ℂ) * rightConv K x' (L .H (L .H (α))) g + (Complex.I : ℂ) * rightConv K x' (L .H (L .iH (α))) g + (Complex.I : ℂ) * rightConv K x' (L .iH (L .H (α))) g + (-1 : ℂ) * rightConv K x' (L .iH (L .iH (α))) g)) - (1 / 2 : ℂ) * ((1 / 2 : ℂ) * ((1 : ℂ) * rightConv K x' (L .H (α)) g + (Complex.I : ℂ) * rightConv K x' (L .iH (α)) g)) + (1 / 4 : ℂ) * ((1 : ℂ) * rightConv K x' (L .E (L .Fm (α))) g + (Complex.I : ℂ) * rightConv K x' (L .E (L .iFm (α))) g + (Complex.I : ℂ) * rightConv K x' (L .iE (L .Fm (α))) g + (-1 : ℂ) * rightConv K x' (L .iE (L .iFm (α))) g)))) ∧
    (∀ x' : AdelicGL2 (𝓞 K) K → ℂ, Continuous x' →
      x' ∈ levelInvariantSubmodule K (productionPinsOf K D (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) N → x' ∈ archCutSubmodule K tys →
      rightConv K x' β ∈ levelInvariantSubmodule K (productionPinsOf K D (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) N ⊓ archCutSubmodule K tys ∧
      rightConv K x' βb ∈ levelInvariantSubmodule K (productionPinsOf K D (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) N ⊓ archCutSubmodule K tys) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_isFactorizableTestFn_leftCasimirComplex_and_rightConv_mem_of_isArchBiFinite.solution
