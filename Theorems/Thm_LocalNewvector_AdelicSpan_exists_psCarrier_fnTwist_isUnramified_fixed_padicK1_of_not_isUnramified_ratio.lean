import Definitions.Def_LocalNewvector_AdelicSpanCarrier
import Definitions.Def_LocalNewvector_PrincipalSeriesCarrier
import Definitions.Def_LocalNewvector_CharConductor
import Definitions.Def_AutomorphicForm_FnTwist
import Definitions.Def_AdelicDock_LocalEmbedding
import Mathlib.NumberTheory.Padics.RingHoms
import P2M.Util
import P2M.Sol.S_LocalNewvector_AdelicSpan_exists_psCarrier_fnTwist_isUnramified_fixed_padicK1_of_not_isUnramified_ratio
attribute [-instance] FLT.SpectralSide.instCompactSpaceMatrix
attribute [-simp] LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv

set_option autoImplicit false

theorem LocalNewvector.AdelicSpan.exists_psCarrier_fnTwist_isUnramified_fixed_padicK1_of_not_isUnramified_ratio
    (Φ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ)
    (q : ℕ) [Fact q.Prime]
    (n₀ : ℕ) (hΦK : ∀ k ∈ LocalNewvector.padicK1 q n₀, ∀ x, Φ (x * AdelicDock.padicToAdelic q k) = Φ x)
    (hΦZ : ∀ (u : ℤ_[q]ˣ) (x : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ),
      Φ (x * AdelicDock.padicToAdelic q
        (LocalNewvector.centralGL q (Units.map PadicInt.Coe.ringHom.toMonoidHom u))) = Φ x)
    (μ₁ μ₂ : ℚ_[q]ˣ →* ℂˣ) (f : LocalNewvector.AdelicSpan Φ →ₗ[ℂ] LocalNewvector.PSCarrier q μ₁ μ₂)
    (hfequiv : ∀ (x : GL (Fin 2) ℚ_[q]) (v : LocalNewvector.AdelicSpan Φ), f (x • v) = x • f v)
    (hf0 : f ≠ 0)
    (hratio : ¬ LocalNewvector.IsUnramified q (μ₁⁻¹ * μ₂))
    (b : ℕ) (χ₀ : (ZMod (q ^ b))ˣ →* ℂˣ)
    (hχ₀compat : ∀ u : ℤ_[q]ˣ,
      μ₁ (Units.map PadicInt.Coe.ringHom.toMonoidHom u) =
        χ₀ (Units.map (PadicInt.toZModPow b).toMonoidHom u))
    (η : (NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ)ˣ →* ℂˣ)
    (hηu : ∀ u : ℤ_[q]ˣ,
      η (Units.map (NumberField.AdelicLevel.finIncl (NumberField.RingOfIntegers ℚ) ℚ)
          (NumberField.AdelicLevel.localUnit (NumberField.RingOfIntegers ℚ) ℚ (AdelicDock.padicPlace q)
            (Units.map (AdelicDock.padicRingEquiv q).toMonoidHom (Units.map PadicInt.Coe.ringHom.toMonoidHom u))))
        = (χ₀ (Units.map (PadicInt.toZModPow b).toMonoidHom u))⁻¹) :
    ∃ (ν₁ ν₂ : ℚ_[q]ˣ →* ℂˣ)
      (f' : LocalNewvector.AdelicSpan (AutomorphicForm.fnTwist ℚ η Φ) →ₗ[ℂ] LocalNewvector.PSCarrier q ν₁ ν₂)
      (a : ℕ) (y : LocalNewvector.AdelicSpan (AutomorphicForm.fnTwist ℚ η Φ)),
      (∀ (x : GL (Fin 2) ℚ_[q]) (v : LocalNewvector.AdelicSpan (AutomorphicForm.fnTwist ℚ η Φ)),
          f' (x • v) = x • f' v) ∧
      f' ≠ 0 ∧ LocalNewvector.IsUnramified q ν₁ ∧
      LocalNewvector.HasCharConductor q (μ₁⁻¹ * μ₂) a ∧
      y ∈ Submodule.span ℂ
        (Set.range fun x : GL (Fin 2) ℚ_[q] =>
          x • LocalNewvector.AdelicSpan.self (AutomorphicForm.fnTwist ℚ η Φ)) ∧
      y ≠ 0 ∧
      y ∈ LocalNewvector.fixedSubmodule (LocalNewvector.padicK1 q a)
        (LocalNewvector.AdelicSpan (AutomorphicForm.fnTwist ℚ η Φ)) ∧
      ∀ u : ℤ_[q]ˣ,
        LocalNewvector.centralGL q (Units.map PadicInt.Coe.ringHom.toMonoidHom u) • y =
          ((μ₁ (Units.map PadicInt.Coe.ringHom.toMonoidHom u) : ℂ) ^ 2)⁻¹ • y := by p2m_exact_reverting @_root_.P2MW.S_LocalNewvector_AdelicSpan_exists_psCarrier_fnTwist_isUnramified_fixed_padicK1_of_not_isUnramified_ratio.solution
