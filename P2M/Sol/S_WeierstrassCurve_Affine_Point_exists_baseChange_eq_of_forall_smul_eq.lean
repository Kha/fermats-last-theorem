import Mathlib.FieldTheory.Galois.Infinite
import Definitions.Def_FLTPrelim_GaloisRep
import P2M.Util
namespace P2MW.S_WeierstrassCurve_Affine_Point_exists_baseChange_eq_of_forall_smul_eq

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

theorem solution {R : Type*} {S : Type*} {K : Type*} [CommRing R] [Field S] [Field K] [DecidableEq S] [DecidableEq K] [Algebra R S] [Algebra R K] [Algebra S K] [IsScalarTower R S K] [IsGalois S K] (W' : Affine R) (x : (W'⁄K).Point) (hx : ∀ σ : K ≃ₐ[S] K, σ • x = x) : ∃ y : (W'⁄S).Point, Point.baseChange S K y = x := by
  rcases x with (_ | ⟨x₁, y₁, h⟩)
  · exact ⟨0, rfl⟩
  ·
    have hfix : ∀ σ : K ≃ₐ[S] K, σ x₁ = x₁ ∧ σ y₁ = y₁ := fun σ => by
      have hσ := hx σ
      rw [algEquiv_smul_def, map_some] at hσ
      exact some.inj hσ
    obtain ⟨a, rfl⟩ :=
      (InfiniteGalois.mem_range_algebraMap_iff_fixed x₁).mpr fun σ => (hfix σ).1
    obtain ⟨b, rfl⟩ :=
      (InfiniteGalois.mem_range_algebraMap_iff_fixed y₁).mpr fun σ => (hfix σ).2
    exact ⟨.some a b ((W'.baseChange_nonsingular (f := Algebra.ofId S K)
      (algebraMap S K).injective a b).mp h), rfl⟩
