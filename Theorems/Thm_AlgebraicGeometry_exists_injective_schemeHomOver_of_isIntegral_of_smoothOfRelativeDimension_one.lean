import Definitions.Def_CerednikDrinfeld_QMCoarseModuli
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_injective_schemeHomOver_of_isIntegral_of_smoothOfRelativeDimension_one

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra
theorem AlgebraicGeometry.exists_injective_schemeHomOver_of_isIntegral_of_smoothOfRelativeDimension_one
    (k : Type) [Field k] [IsAlgClosed k] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of k))
    [IsIntegral X] (hf : SmoothOfRelativeDimension 1 f) [LocallyOfFiniteType f] :
    ∃ x : ℕ → SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f, Function.Injective x := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_injective_schemeHomOver_of_isIntegral_of_smoothOfRelativeDimension_one.solution
