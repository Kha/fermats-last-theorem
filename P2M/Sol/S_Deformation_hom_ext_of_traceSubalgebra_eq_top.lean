import Mathlib
import Definitions.Def_Deformations_TraceAlgebra
import P2M.Util
namespace P2MW.S_Deformation_hom_ext_of_traceSubalgebra_eq_top

open CategoryTheory

universe u

theorem solution {n : Type} [Fintype n] [DecidableEq n] {G : Type u} [Group G]
    [TopologicalSpace G] {𝓞 : Type u} [CommRing 𝓞] {A B : Deformation.ProartinianCat 𝓞} {f g : A ⟶ B} {σ : G →ₜ* GL n A}
    (hσ : Deformation.traceSubalgebra 𝓞 σ = ⊤)
    (h : ∀ x : G, f.hom (Matrix.trace ((σ x : GL n A) : Matrix n n A)) =
      g.hom (Matrix.trace ((σ x : GL n A) : Matrix n n A))) : f = g := by

  have hle : Deformation.traceSubalgebra 𝓞 σ ≤ AlgHom.equalizer f.hom.toAlgHom g.hom.toAlgHom :=
    Deformation.traceSubalgebra_le σ (isClosed_eq f.hom.cont g.hom.cont) h
  refine Deformation.ProartinianCat.hom_ext (ContinuousAlgHom.ext fun a => ?_)
  exact hle (hσ.ge (Algebra.mem_top (R := 𝓞) (A := A.carrier) (x := a)))
