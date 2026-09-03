import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicCurve_GluedPic0
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_RROpens_finrank_le_of_forall_mem_riemannRochSpace_sub_and_hasValue_nodes_and_hasValue_leading
attribute [-simp] AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one

set_option autoImplicit false

universe u v

open AlgebraicCurve

theorem AlgebraicCurve.RROpens.finrank_le_of_forall_mem_riemannRochSpace_sub_and_hasValue_nodes_and_hasValue_leading
    {K : Type u} {F : Type v} [Field K] [Field F] [Algebra K F] [IsAlgClosed K]
    [IsCurveOver K F] (Kc : Divisor K F) (g : ℕ)
    (hRR : ∀ D : Divisor K F, (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1 - g)
    (SS : Finset (Place K F × Place K F))
    (hinj : Set.InjOn Prod.fst (SS : Set (Place K F × Place K F)))
    (s : Place K F × Place K F) (hs : s ∈ SS)
    (D₁ D₂ : Divisor K F) (hD₁ : ∀ t ∈ SS, D₁ t.1 = 0) (hD₂ : ∀ t ∈ SS, D₂ t.2 = 0)
    (x y : F) (hx : s.1.ord x = 1) (hy : s.2.ord y = 1)
    (u : K) (m k : ℤ) (hm : 0 ≤ m) (hk : 0 ≤ k)
    (hdeg₁ : 2 * (g : ℤ) + m + SS.card ≤ Divisor.degree D₁)
    (hdeg₂ : 2 * (g : ℤ) + k + SS.card ≤ Divisor.degree D₂)
    (P : Submodule K (Fin 2 → F))
    (hP : ∀ h ∈ P,
      h 0 ∈ riemannRochSpace (D₁ - Finsupp.single s.1 m) ∧
      h 1 ∈ riemannRochSpace (D₂ - Finsupp.single s.2 k) ∧
      (∀ t ∈ SS, t ≠ s → ∃ c : K, t.1.HasValue (h 0) c ∧ t.2.HasValue (h 1) c) ∧
      (∃ lam : K, s.2.HasValue (h 1 * y ^ (-k)) lam ∧ s.1.HasValue (h 0 * x ^ (-m)) (u * lam))) :
    FiniteDimensional K ↥P ∧
      (Module.finrank K ↥P : ℤ) ≤
        (Divisor.degree D₁ - m) + (Divisor.degree D₂ - k) + 2 - 2 * (g : ℤ) - SS.card := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_RROpens_finrank_le_of_forall_mem_riemannRochSpace_sub_and_hasValue_nodes_and_hasValue_leading.solution
