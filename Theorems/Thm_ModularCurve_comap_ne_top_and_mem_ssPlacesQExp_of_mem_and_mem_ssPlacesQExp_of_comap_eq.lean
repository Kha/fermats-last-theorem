import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Definitions.Def_ModularCurve_QExpCoeffSemilinearAut
import P2M.Util
import P2M.Sol.S_ModularCurve_comap_ne_top_and_mem_ssPlacesQExp_of_mem_and_mem_ssPlacesQExp_of_comap_eq

set_option autoImplicit false

open scoped MatrixGroups
open ModularCurve AlgebraicCurve

theorem ModularCurve.comap_ne_top_and_mem_ssPlacesQExp_of_mem_and_mem_ssPlacesQExp_of_comap_eq
    (p : ℕ) [Fact p.Prime] (k : Type*) [Field k] [IsAlgClosed k] [CharP k p]
    (K : Type*) [Field K] [IsAlgClosed K] [Algebra k K]
    (Γ : Subgroup SL(2, ℤ))
    (ι : ↥(qExpFunctionFieldC k Γ) →+* ↥(qExpFunctionFieldC K Γ))
    (hι : ∀ x : ↥(qExpFunctionFieldC k Γ),
      ((ι x : ↥(qExpFunctionFieldC K Γ)) : LaurentSeries K) = coeffMap (algebraMap k K) (x : LaurentSeries k))
    (hss : @ssJSet p K _ (Classical.decEq K) = algebraMap k K '' @ssJSet p k _ (Classical.decEq k))
    (w : Place K ↥(qExpFunctionFieldC K Γ)) :
    (w ∈ ssPlacesQExp K Γ p →
        w.toValuationSubring.comap ι ≠ ⊤ ∧
          ∀ v : Place k ↥(qExpFunctionFieldC k Γ), w.toValuationSubring.comap ι = v.toValuationSubring →
            v ∈ ssPlacesQExp k Γ p) ∧
      (∀ v ∈ ssPlacesQExp k Γ p, w.toValuationSubring.comap ι = v.toValuationSubring → w ∈ ssPlacesQExp K Γ p) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_comap_ne_top_and_mem_ssPlacesQExp_of_mem_and_mem_ssPlacesQExp_of_comap_eq.solution
