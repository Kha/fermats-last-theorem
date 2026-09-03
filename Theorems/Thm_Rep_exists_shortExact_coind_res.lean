import Mathlib
import P2M.Util
import P2M.Sol.S_Rep_exists_shortExact_coind_res
attribute [-instance] groupCohomology.normal_comap_fixingSubgroup groupCohomology.finiteIndex_comap_fixingSubgroup
attribute [-simp] groupCohomology.continuousH2ToH2_mk

set_option autoImplicit false

universe u

open CategoryTheory
theorem Rep.exists_shortExact_coind_res {k G : Type u} [Field k] [Group G]
    (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (S : Subgroup G) [S.FiniteIndex]
    (hS : ∃ F₀ : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F₀ ∧ F₀.fixingSubgroup.comap r ≤ S)
    (N : Rep.{u} k G) [FiniteDimensional k N]
    (hsm : ∀ n : N, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s : G, r s ∈ F.fixingSubgroup → N.ρ s n = n) :
    ∃ (Q : Rep.{u} k G) (φ : N ⟶ Rep.coind S.subtype (Rep.res S.subtype N))
      (ψ : Rep.coind S.subtype (Rep.res S.subtype N) ⟶ Q),
      Function.Injective φ.hom ∧ Function.Surjective ψ.hom ∧
      (∀ b, ψ.hom b = 0 ↔ ∃ a : N, φ.hom a = b) ∧
      FiniteDimensional k Q ∧ FiniteDimensional k (Rep.coind S.subtype (Rep.res S.subtype N)) ∧
      (∀ m : Rep.coind S.subtype (Rep.res S.subtype N), ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ),
          FiniteDimensional ℚ F ∧ ∀ s : G, r s ∈ F.fixingSubgroup → (Rep.coind S.subtype (Rep.res S.subtype N)).ρ s m = m) ∧
      (∀ m : Q, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ),
          FiniteDimensional ℚ F ∧ ∀ s : G, r s ∈ F.fixingSubgroup → Q.ρ s m = m) := by p2m_exact_reverting @_root_.P2MW.S_Rep_exists_shortExact_coind_res.solution
