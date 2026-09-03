import Mathlib
import Definitions.Def_ModularCurve_LevelModuliPackage
import Definitions.Def_ModularCurve_LevelModuliPackageAbs
import P2M.Util
namespace P2MW.S_ModularCurve_LevelModuliPackageAbs_exists_algEquiv_map_univ_eq_act

set_option autoImplicit false

universe u

theorem solution
    {A : Type u} [CommRing A] {D : ModularCurve.LevelModuliDatum.{u} A} (P : ModularCurve.LevelModuliPackageAbs A D)
    (ρ ρ' : D.ProblemAut)
    (h₁ : ∀ (T : Type u) [CommRing T] [Algebra A T] (y : D.Pt T), ρ'.act (ρ.act y) = y)
    (h₂ : ∀ (T : Type u) [CommRing T] [Algebra A T] (y : D.Pt T), ρ.act (ρ'.act y) = y) :
    ∃ σ : P.B₀ ≃ₐ[A] P.B₀,
      D.map (σ : P.B₀ →ₐ[A] P.B₀) P.univ = ρ.act P.univ ∧
      D.map (σ.symm : P.B₀ →ₐ[A] P.B₀) P.univ = ρ'.act P.univ := by
  classical
  let φ : P.B₀ →ₐ[A] P.B₀ := P.classify (ρ.act P.univ)
  let φ' : P.B₀ →ₐ[A] P.B₀ := P.classify (ρ'.act P.univ)
  have hφ : D.map φ P.univ = ρ.act P.univ := P.map_classify _
  have hφ' : D.map φ' P.univ = ρ'.act P.univ := P.map_classify _
  have hid : ∀ ψ : P.B₀ →ₐ[A] P.B₀, D.map ψ P.univ = P.univ → ψ = AlgHom.id A P.B₀ := by
    intro ψ hψ
    rw [P.classify_unique P.univ ψ hψ, P.classify_unique P.univ (AlgHom.id A P.B₀) (D.map_id _ _)]
  have c1 : φ'.comp φ = AlgHom.id A P.B₀ := hid _ (by
    rw [D.map_comp, hφ, ← ρ.act_map, hφ', h₂])
  have c2 : φ.comp φ' = AlgHom.id A P.B₀ := hid _ (by
    rw [D.map_comp, hφ', ← ρ'.act_map, hφ, h₁])
  refine ⟨AlgEquiv.ofAlgHom φ φ' c2 c1, ?_, ?_⟩
  · rw [AlgEquiv.coe_algHom_ofAlgHom]; exact hφ
  · rw [AlgEquiv.ofAlgHom_symm, AlgEquiv.coe_algHom_ofAlgHom]; exact hφ'
