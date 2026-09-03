import Mathlib
import Definitions.Def_ModularCurve_LevelModuliPackage
import Definitions.Def_ModularCurve_LevelModuliPackageAbs
import P2M.Util
namespace P2MW.S_ModularCurve_LevelModuliPackageAbs_apply_mem_range_of_map_eq_map_univ

set_option autoImplicit false

universe u

open ModularCurve

theorem solution
    {A : Type u} [CommRing A] {D : LevelModuliDatum.{u} A} (P : LevelModuliPackageAbs A D)
    (K : Type u) [CommRing K] [Algebra A K] (R₀ : Type u) [CommRing R₀] [Algebra A R₀]
    (ι : R₀ →ₐ[A] K)
    (φ : P.B₀ →ₐ[A] K) (y : D.Pt R₀) (hy : D.map ι y = D.map φ P.univ) :
    ∀ b : P.B₀, φ b ∈ Set.range ι := by
  intro b
  have h1 : D.map (ι.comp (P.classify y)) P.univ = D.map φ P.univ := by
    rw [D.map_comp, P.map_classify, hy]
  have h2 : ι.comp (P.classify y) = P.classify (D.map φ P.univ) := P.classify_unique _ _ h1
  have h3 : φ = P.classify (D.map φ P.univ) := P.classify_unique _ _ rfl
  rw [h3, ← h2]
  exact ⟨P.classify y b, rfl⟩
