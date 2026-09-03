import Definitions.Def_AlgebraicGeometry_FppfSiteCohomology
import Definitions.Def_AlgebraicGeometry_FppfCohomologyLES
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_finite_fppfCohomology_of_shortExact_chain
open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory
universe u
theorem AlgebraicGeometry.Scheme.finite_fppfCohomology_of_shortExact_chain
    (S : Scheme.{u}) {k : ℕ} (F : Fin (k + 1) → Sheaf (smallFppfTopology S) Ab.{u + 1})
    (incl : ∀ i : Fin k, F i.castSucc ⟶ F i.succ) (n : ℕ)
    (h0 : Finite (fppfCohomology S (F 0) n))
    (hL : ∀ i : Fin k, ∃ (L : Sheaf (smallFppfTopology S) Ab.{u + 1}) (π : F i.succ ⟶ L)
      (w : incl i ≫ π = 0), (ShortComplex.mk (incl i) π w).ShortExact ∧
        Finite (fppfCohomology S L n)) :
    Finite (fppfCohomology S (F (Fin.last k)) n) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_finite_fppfCohomology_of_shortExact_chain.solution
