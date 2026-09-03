import Mathlib
import Definitions.Def_ModularCurve_LevelModuliPackage
import Definitions.Def_ModularCurve_LevelModuliPackageAbs
import P2M.Util
import P2M.Sol.S_ModularCurve_LevelModuliPackageAbs_apply_mem_range_of_map_eq_map_univ

set_option autoImplicit false

universe u

open ModularCurve

theorem ModularCurve.LevelModuliPackageAbs.apply_mem_range_of_map_eq_map_univ
    {A : Type u} [CommRing A] {D : LevelModuliDatum.{u} A} (P : LevelModuliPackageAbs A D)
    (K : Type u) [CommRing K] [Algebra A K] (R₀ : Type u) [CommRing R₀] [Algebra A R₀]
    (ι : R₀ →ₐ[A] K)
    (φ : P.B₀ →ₐ[A] K) (y : D.Pt R₀) (hy : D.map ι y = D.map φ P.univ) :
    ∀ b : P.B₀, φ b ∈ Set.range ι := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_LevelModuliPackageAbs_apply_mem_range_of_map_eq_map_univ.solution
