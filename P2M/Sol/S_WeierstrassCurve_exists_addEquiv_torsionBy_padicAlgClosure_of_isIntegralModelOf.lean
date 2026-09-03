import Mathlib
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_GaloisRep_Residual
import Definitions.Def_FLTPrelim_GaloisRep
import Theorems.Thm_WeierstrassCurve_exists_addEquiv_point_baseChange_variableChange_smul_algEquiv
import P2M.Util
namespace P2MW.S_WeierstrassCurve_exists_addEquiv_torsionBy_padicAlgClosure_of_isIntegralModelOf

open scoped NNReal
open scoped WeierstrassCurve.Affine
open WeierstrassCurve WeierstrassCurve.Affine.Point

theorem solution
    (E : WeierstrassCurve ℚ) {W : WeierstrassCurve ℤ} (hW : W.IsIntegralModelOf E)
    (p : ℕ) [Fact p.Prime] :
    letI : DecidableEq (AlgebraicClosure ℚ_[p]) := Classical.decEq _
    ∃ ψ : Submodule.torsionBy ℤ ((E.map (algebraMap ℚ ℚ_[p]))⁄(AlgebraicClosure ℚ_[p])).Point p ≃+
          Submodule.torsionBy ℤ ((W.map (Int.castRingHom ℚ_[p]))⁄(AlgebraicClosure ℚ_[p])).Point p,
      ∀ (σ : AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p]) P,
        ψ (σ • P) = σ • ψ P := by
  letI : DecidableEq (AlgebraicClosure ℚ_[p]) := Classical.decEq _
  obtain ⟨C₀, hC₀⟩ := hW
  let γ : WeierstrassCurve.VariableChange ℚ_[p] := C₀.map (algebraMap ℚ ℚ_[p])
  have hγ : γ • (E.map (algebraMap ℚ ℚ_[p])) = W.map (Int.castRingHom ℚ_[p]) := by
    have h1 : (γ • (E.map (algebraMap ℚ ℚ_[p]))) = (C₀ • E).map (algebraMap ℚ ℚ_[p]) := by
      simp only [γ, WeierstrassCurve.map_variableChange]
    rw [h1, hC₀, WeierstrassCurve.map_map]
    congr 1

  obtain ⟨φ, hφ⟩ := hγ ▸
    WeierstrassCurve.exists_addEquiv_point_baseChange_variableChange_smul_algEquiv
      (K := AlgebraicClosure ℚ_[p]) (E.map (algebraMap ℚ ℚ_[p])) γ

  refine ⟨{
    toFun := fun ⟨P, hP⟩ => ⟨φ.symm P, by
      rw [Submodule.mem_torsionBy_iff] at hP ⊢
      rw [← map_zsmul, hP]; exact φ.symm.map_zero⟩
    invFun := fun ⟨Q, hQ⟩ => ⟨φ Q, by
      rw [Submodule.mem_torsionBy_iff] at hQ ⊢
      rw [← map_zsmul, hQ]; exact φ.map_zero⟩
    left_inv := fun ⟨P, _⟩ => by simp
    right_inv := fun ⟨Q, _⟩ => by simp
    map_add' := fun ⟨P, _⟩ ⟨Q, _⟩ => by
      refine Subtype.ext ?_
      exact φ.symm.map_add P Q
  }, ?_⟩
  intro σ ⟨P, hP⟩
  refine Subtype.ext ?_
  show φ.symm (σ • P) = σ • φ.symm P
  apply φ.injective
  rw [φ.apply_symm_apply, hφ σ (φ.symm P), φ.apply_symm_apply]
