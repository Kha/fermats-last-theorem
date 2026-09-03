import Mathlib
import Definitions.Def_ModularCurve_LevelModuliPackage
import Definitions.Def_ModularCurve_LevelModuliPackageAbs
import P2M.Util
import P2M.Sol.S_ModularCurve_LevelModuliPackageAbs_exists_algEquiv_map_univ_eq

set_option autoImplicit false

universe u

open ModularCurve

theorem ModularCurve.LevelModuliPackageAbs.exists_algEquiv_map_univ_eq
    {A : Type u} [CommRing A] {D : LevelModuliDatum.{u} A} (P P' : LevelModuliPackageAbs A D) :
    ∃ e : P.B₀ ≃ₐ[A] P'.B₀, D.map (e : P.B₀ →ₐ[A] P'.B₀) P.univ = P'.univ := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_LevelModuliPackageAbs_exists_algEquiv_map_univ_eq.solution
