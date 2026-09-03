import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_genericPoint_mem_preimage_comp_pullback_fst_of_injective_algebraMap

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.genericPoint_mem_preimage_comp_pullback_fst_of_injective_algebraMap
    {R : Type u} [CommRing R] {K : Type u} [Field K] [Algebra R K]
    (hinj : Function.Injective (algebraMap R K))
    {X : Scheme.{u}} (c : X ⟶ Spec (.of R)) [IsIntegral X]
    {Y : Scheme.{u}} [IsIntegral Y]
    (e₀ : Y ⟶ pullback c (Spec.map (CommRingCat.ofHom (algebraMap R K)))) [IsIso e₀]
    (U : X.Opens) (hU : (U : Set X).Nonempty) :
    genericPoint Y ∈ (e₀ ≫ pullback.fst c (Spec.map (CommRingCat.ofHom (algebraMap R K)))) ⁻¹ᵁ U := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_genericPoint_mem_preimage_comp_pullback_fst_of_injective_algebraMap.solution
