import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import P2M.Util
import P2M.Sol.S_groupCohomology_exists_isLevelConstant_inhomogeneousCochains_d_eq_of_res_fixingSubgroup_three
attribute [-simp] groupCohomology.Cores.Transversal.mk.sizeOf_spec groupCohomology.Cores.Transversal.mk.injEq

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory groupCohomology

theorem groupCohomology.exists_isLevelConstant_inhomogeneousCochains_d_eq_of_res_fixingSubgroup_three
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes)
    (N : Rep.{0} (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (hK : K.IsUnramifiedOutside S)
    [K.fixingSubgroup.FiniteIndex] (hpK : ¬ p ∣ K.fixingSubgroup.index)
    (u : (Fin 3 → (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) → N)
    (hlc : ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), F.IsUnramifiedOutside S ∧
      ∀ g s : Fin 3 → (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ),
        (∀ i, s i ∈ F.fixingSubgroup) → u (g * s) = u g)
    (hcoc : ((inhomogeneousCochains N).d 3 4).hom u = 0)
    (w' : (Fin 2 → K.fixingSubgroup) → N)
    (hlc' : ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), F.IsUnramifiedOutside S ∧
      ∀ g s : Fin 2 → K.fixingSubgroup,
        (∀ i, (s i : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ∈ F.fixingSubgroup) → w' (g * s) = w' g)
    (hw' : ((inhomogeneousCochains (Rep.res K.fixingSubgroup.subtype N)).d 2 3).hom w'
             = fun h : Fin 3 → K.fixingSubgroup =>
                 u (fun i => (h i : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))) :
    ∃ w : (Fin 2 → (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) → N,
      (∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), F.IsUnramifiedOutside S ∧
        ∀ g s : Fin 2 → (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ),
          (∀ i, s i ∈ F.fixingSubgroup) → w (g * s) = w g) ∧
      ((inhomogeneousCochains N).d 2 3).hom w = u := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_exists_isLevelConstant_inhomogeneousCochains_d_eq_of_res_fixingSubgroup_three.solution
