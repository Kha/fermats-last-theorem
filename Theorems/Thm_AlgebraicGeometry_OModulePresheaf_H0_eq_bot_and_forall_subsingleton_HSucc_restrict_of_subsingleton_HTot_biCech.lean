import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Definitions.Def_AlgebraicGeometry_DoubleComplex
import Definitions.Def_AlgebraicGeometry_BiCech
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_H0_eq_bot_and_forall_subsingleton_HSucc_restrict_of_subsingleton_HTot_biCech

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.OModulePresheaf.H0_eq_bot_and_forall_subsingleton_HSucc_restrict_of_subsingleton_HTot_biCech
    {R : Type u} [CommRing R] {X : Scheme.{u}} (π : X ⟶ Spec (CommRingCat.of R))
    (N : X.Modules) (U V : X.Opens)
    (𝔙 : (V : Scheme.{u}).OrderedAffineCover) (𝔘 : (U : Scheme.{u}).OrderedAffineCover)
    (𝔛' : X.OrderedAffineCover) (eV : 𝔙.ι ↪o 𝔛'.ι) (eU : 𝔘.ι ↪o 𝔛'.ι)
    (hV : ∀ b, 𝔛'.U (eV b) = V.ι ''ᵁ 𝔙.U b) (hU : ∀ a, 𝔛'.U (eU a) = U.ι ''ᵁ 𝔘.U a)
    (hlt : ∀ b a, eV b < eU a) (hcov : ∀ j, j ∈ Set.range eV ∨ j ∈ Set.range eU)
    (hX : (OModulePresheaf.ofModules π N).H0 𝔛' = ⊥ ∧
      ∀ i, Subsingleton ((OModulePresheaf.ofModules π N).HSucc 𝔛' i))
    (hD : ∀ n, Subsingleton (DoubleComplex.HTot
      ((OModulePresheaf.ofModules π N).biCech (𝔙.imageFamily V.ι) (𝔘.imageFamily U.ι)) n)) :
    (OModulePresheaf.ofModules (V.ι ≫ π) (N.restrict V.ι)).H0 𝔙 = ⊥ ∧
      ∀ i, Subsingleton ((OModulePresheaf.ofModules (V.ι ≫ π) (N.restrict V.ι)).HSucc 𝔙 i) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_H0_eq_bot_and_forall_subsingleton_HSucc_restrict_of_subsingleton_HTot_biCech.solution
