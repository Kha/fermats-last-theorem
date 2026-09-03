import Mathlib
import Definitions.Def_Deformations_TraceAlgebra
import P2M.Util
import P2M.Sol.S_Deformation_hom_ext_of_traceSubalgebra_eq_top

open CategoryTheory IsLocalRing

universe u v
theorem Deformation.hom_ext_of_traceSubalgebra_eq_top {n : Type} [Fintype n] [DecidableEq n] {G : Type u} [Group G]
    [TopologicalSpace G] {𝓞 : Type u} [CommRing 𝓞] {A B : Deformation.ProartinianCat 𝓞} {f g : A ⟶ B} {σ : G →ₜ* GL n A}
    (hσ : Deformation.traceSubalgebra 𝓞 σ = ⊤)
    (h : ∀ x : G, f.hom (Matrix.trace ((σ x : GL n A) : Matrix n n A)) =
      g.hom (Matrix.trace ((σ x : GL n A) : Matrix n n A))) : f = g := by p2m_exact_reverting @_root_.P2MW.S_Deformation_hom_ext_of_traceSubalgebra_eq_top.solution
