import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme

import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_geomFibreH0Finrank_eq_of_isPullback
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_geomFibreH0Finrank_eq_of_forall_isPullback_away

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open scoped TensorProduct

universe u

theorem solution
    {S : Type u} [CommRing S] {k : ℕ} (r : Fin k → S) (hr : Ideal.span (Set.range r) = ⊤)
    (B : Fin k → Type u) [∀ i, CommRing (B i)] [∀ i, Algebra S (B i)] [∀ i, IsLocalization.Away (r i) (B i)]
    {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of S))
    {A' : Fin k → Scheme.{u}} (f' : ∀ i, A' i ⟶ Spec (CommRingCat.of (B i))) (g : ∀ i, A' i ⟶ A)
    (hg : ∀ i, IsPullback (g i) (f' i) f (Spec.map (CommRingCat.ofHom (algebraMap S (B i)))))
    (M : A.Modules) (M' : ∀ i, (A' i).Modules) (e : ∀ i, (Scheme.Modules.pullback (g i)).obj M ≅ M' i) (d : ℕ)
    (h : ∀ (i : Fin k) (K : Type u) [Field K] [IsAlgClosed K] (sK : B i →+* K),
      Scheme.Modules.geomFibreH0Finrank (f' i) (M' i) K sK = d)
    (K : Type u) [Field K] [IsAlgClosed K] (sK : S →+* K) :
    Scheme.Modules.geomFibreH0Finrank f M K sK = d := by
  classical

  have hex : ∃ i, sK (r i) ≠ 0 := by
    by_contra hne
    push_neg at hne
    have h1 : (1 : S) ∈ Ideal.span (Set.range r) := by rw [hr]; trivial
    obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp h1
    have := congrArg sK hc
    simp only [map_sum, map_mul, hne, mul_zero, Finset.sum_const_zero, map_one] at this
    exact zero_ne_one this
  obtain ⟨i, hi⟩ := hex
  have hu : IsUnit (sK (r i)) := isUnit_iff_ne_zero.mpr hi
  let sK' : B i →+* K := IsLocalization.Away.lift (r i) hu
  have hsK' : sK'.comp (algebraMap S (B i)) = sK := IsLocalization.Away.lift_comp (r i) hu
  have h2 := AlgebraicGeometry.Scheme.Modules.geomFibreH0Finrank_eq_of_isPullback (algebraMap S (B i)) f (f' i) (g i) (hg i)
    M (M' i) (e i) K sK'
  rw [hsK', h i K sK'] at h2
  exact h2.symm
