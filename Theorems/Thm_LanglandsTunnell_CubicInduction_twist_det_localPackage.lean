import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_twist_det_localPackage
attribute [-simp] LanglandsTunnell.CubicInduction.fnTwist3_apply

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction

theorem LanglandsTunnell.CubicInduction.twist_det_localPackage
    (v : HeightOneSpectrum (𝓞 ℚ)) (ψv : AddChar (v.adicCompletion ℚ) ℂ)
    (χv : (v.adicCompletion ℚ)ˣ →* ℂˣ)
    (U₀ : Subgroup (v.adicCompletion ℚ)ˣ) (hU₀ : IsOpen (U₀ : Set (v.adicCompletion ℚ)ˣ)) (hχU₀ : ∀ u ∈ U₀, χv u = 1)
    (hχu : ∀ z : (v.adicCompletion ℚ)ˣ, ‖((χv z : ℂˣ) : ℂ)‖ = 1)
    (W : LocalGL3 v → ℂ) :

    ((∀ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) →
        ∃ B : Finset (LocalGL3 v → ℂ), ∀ G ∈ gl3CyclicSubspace W,
          (∀ k ∈ Uv, ∀ g : LocalGL3 v, G (g * k) = G g) → G ∈ Submodule.span ℂ (B : Set (LocalGL3 v → ℂ))) →
      ∀ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) →
        ∃ B : Finset (LocalGL3 v → ℂ), ∀ G ∈ gl3CyclicSubspace
            (fun x : LocalGL3 v => ((χv (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) * W x),
          (∀ k ∈ Uv, ∀ g : LocalGL3 v, G (g * k) = G g) → G ∈ Submodule.span ℂ (B : Set (LocalGL3 v → ℂ))) ∧

    (HasWhittakerMultOne ψv W →
      HasWhittakerMultOne ψv (fun x : LocalGL3 v => ((χv (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) * W x)) ∧

    ((∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧ ∀ k ∈ Uv, ∀ g : LocalGL3 v, W (g * k) = W g) →
      ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
        ∀ k ∈ Uv, ∀ g : LocalGL3 v,
          (fun x : LocalGL3 v => ((χv (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) * W x) (g * k) =
            (fun x : LocalGL3 v => ((χv (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) * W x) g) ∧

    (∀ ωv : (v.adicCompletion ℚ)ˣ →* ℂˣ, (∀ z : (v.adicCompletion ℚ)ˣ, ‖((ωv z : ℂˣ) : ℂ)‖ = 1) →
      (∀ (t : (v.adicCompletion ℚ)ˣ) (h : LocalGL3 v),
          W (Matrix.GeneralLinearGroup.scalar (Fin 3) t * h) = ((ωv t : ℂˣ) : ℂ) * W h) →
      (∀ z : (v.adicCompletion ℚ)ˣ, ‖(((ωv * χv ^ 3) z : ℂˣ) : ℂ)‖ = 1) ∧
      ∀ (t : (v.adicCompletion ℚ)ˣ) (h : LocalGL3 v),
        (fun x : LocalGL3 v => ((χv (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) * W x)
            (Matrix.GeneralLinearGroup.scalar (Fin 3) t * h) =
          (((ωv * χv ^ 3) t : ℂˣ) : ℂ) *
            (fun x : LocalGL3 v => ((χv (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) * W x) h) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_twist_det_localPackage.solution
