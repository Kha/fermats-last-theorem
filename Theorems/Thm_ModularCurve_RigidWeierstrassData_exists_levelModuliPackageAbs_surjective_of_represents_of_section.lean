import Mathlib
import Definitions.Def_ModularCurve_LevelModuliPackage
import Definitions.Def_ModularCurve_LevelModuliPackageAbs
import Definitions.Def_ModularCurve_WeierstrassLevelModuliDatum
import P2M.Util
import P2M.Sol.S_ModularCurve_RigidWeierstrassData_exists_levelModuliPackageAbs_surjective_of_represents_of_section

set_option autoImplicit false

universe u

open ModularCurve

theorem ModularCurve.RigidWeierstrassData.exists_levelModuliPackageAbs_surjective_of_represents_of_section
    {A : Type u} [CommRing A] (R : RigidWeierstrassData.{u} A)

    (C : Type u) [CommRing C] [Algebra A C] (xᵤ : R.Raw C)
    (hrep : ∀ (T : Type u) [CommRing T] [Algebra A T] (x : R.Raw T),
        ∃! ψ : C →ₐ[A] T, R.mapRing ψ xᵤ = x)

    (hrigid : ∀ (T : Type u) [CommRing T] [Algebra A T] (x : R.Raw T) (C : WeierstrassCurve.VariableChange T),
      R.act C x = x → C = 1)

    (NF : ∀ (T : Type u) [CommRing T] [Algebra A T], R.Raw T → Prop)
    (hNF_map : ∀ (T T' : Type u) [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T'] (f : T →ₐ[A] T')
      (x : R.Raw T), NF T x → NF T' (R.mapRing f x))
    (hNF_sec : ∀ (T : Type u) [CommRing T] [Algebra A T] (x : R.Raw T),
      ∃! C : WeierstrassCurve.VariableChange T, NF T (R.act C x)) :
    ∃ (P : LevelModuliPackageAbs A R.toLevelModuliDatum) (π : C →ₐ[A] P.B₀), Function.Surjective π := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_RigidWeierstrassData_exists_levelModuliPackageAbs_surjective_of_represents_of_section.solution
