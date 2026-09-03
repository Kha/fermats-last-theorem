import Definitions.Def_FLTPrelim_GaloisRep
import Theorems.Thm_WeierstrassCurve_exists_addEquiv_point_of_variableChange_eq
import Theorems.Thm_WeierstrassCurve_Affine_Point_exists_linearEquiv_torsionBy_of_addEquiv
import P2M.Util
namespace P2MW.S_WeierstrassCurve_exists_linearEquiv_torsionBy_of_variableChange_eq

set_option autoImplicit false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

theorem solution {F : Type*} [Field F] (K : Type*) [Field K] [Algebra F K] [DecidableEq K] {E E' : WeierstrassCurve F} (C : VariableChange F) (hC : C • E = E') (n : ℕ) : ∃ φ : Submodule.torsionBy ℤ (E⁄K).Point n ≃ₗ[ZMod n] Submodule.torsionBy ℤ (E'⁄K).Point n, ∀ (σ : K ≃ₐ[F] K) (x : Submodule.torsionBy ℤ (E⁄K).Point n), φ (σ • x) = σ • φ x := by
  obtain ⟨e, he⟩ := WeierstrassCurve.exists_addEquiv_point_of_variableChange_eq K C hC
  obtain ⟨φ, -, hφ⟩ := WeierstrassCurve.Affine.Point.exists_linearEquiv_torsionBy_of_addEquiv e he n
  exact ⟨φ, hφ⟩
