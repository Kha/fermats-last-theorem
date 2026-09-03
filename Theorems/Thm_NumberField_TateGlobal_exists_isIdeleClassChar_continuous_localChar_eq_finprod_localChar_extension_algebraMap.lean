import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_DedekindDomain_Completion_BaseChange
import P2M.Util
import P2M.Sol.S_NumberField_TateGlobal_exists_isIdeleClassChar_continuous_localChar_eq_finprod_localChar_extension_algebraMap
attribute [-instance] FLT.InfiniteAdeleBaseChange.uniqueSelfExtension NumberField.InfinitePlace.RamifiedExtension.instCoeExtension NumberField.InfinitePlace.UnramifiedExtension.instCoeExtension
attribute [-simp] M4aHerbrand.Bridge.genuineβ_fst M4aHerbrand.Bridge.genuineβ_snd M4aHerbrand.ArchSemilocal.psiFactor_tmul M4aHerbrand.ArchSemilocal.psi_apply FLT.InfiniteAdeleBaseChange.evalAlgHom_apply FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.tensorPiAlgHom_tmul_apply FLT.InfiniteAdeleBaseChange.collapsePlaces_apply FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv_tmul_apply FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.injEq FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.injEq M4aHerbrand.Bridge.finiteConorm_apply

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.TateGlobal NumberField.AdelicLevel AutomorphicForm

theorem NumberField.TateGlobal.exists_isIdeleClassChar_continuous_localChar_eq_finprod_localChar_extension_algebraMap
    (E : Type) [Field E] [NumberField E] (K : Type) [Field K] [NumberField K] [Algebra E K]
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hμ : IsIdeleClassChar (𝓞 K) K μ) (hcont : Continuous μ) :
    ∃ ν : (AdeleRing (𝓞 E) E)ˣ →* ℂˣ, IsIdeleClassChar (𝓞 E) E ν ∧ Continuous ν ∧
      ∀ (v : HeightOneSpectrum (𝓞 E)) (x : (v.adicCompletion E)ˣ),
        ((localChar ν v x : ℂˣ) : ℂ) =
          ∏ᶠ w : v.Extension (𝓞 K), ((localChar μ w.1
            (Units.map (algebraMap (v.adicCompletion E) (w.1.adicCompletion K)).toMonoidHom x) : ℂˣ) : ℂ) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_TateGlobal_exists_isIdeleClassChar_continuous_localChar_eq_finprod_localChar_extension_algebraMap.solution
