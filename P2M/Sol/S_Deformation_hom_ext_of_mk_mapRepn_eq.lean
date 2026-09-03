import Mathlib
import Definitions.Def_Deformations_TraceAlgebra
import Theorems.Thm_Deformation_hom_ext_of_traceSubalgebra_eq_top
import P2M.Util
namespace P2MW.S_Deformation_hom_ext_of_mk_mapRepn_eq

open CategoryTheory

universe u

set_option backward.isDefEq.respectTransparency false in
theorem solution {n : Type} [Fintype n] [DecidableEq n] {G : Type u} [Group G]
    [TopologicalSpace G] {𝓞 : Type u} [CommRing 𝓞] [IsLocalRing 𝓞] {A B : Deformation.ProartinianCat 𝓞} {f g : A ⟶ B}
    {σ : G →ₜ* GL n A} (hσ : Deformation.traceSubalgebra 𝓞 σ = ⊤)
    (h : (Quotient.mk'' (Deformation.mapRepn n G 𝓞 f σ) : (Deformation.repnQuotFunctor n G 𝓞).obj B) =
      Quotient.mk'' (Deformation.mapRepn n G 𝓞 g σ)) : f = g := by
  rw [Quotient.eq''] at h
  obtain ⟨δ, hδ⟩ := MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp h)
  refine Deformation.hom_ext_of_traceSubalgebra_eq_top hσ fun x => ?_
  have hδ' : (δ : ConjAct (GL n B)) • Deformation.mapRepn n G 𝓞 g σ = Deformation.mapRepn n G 𝓞 f σ := hδ
  calc f.hom (Matrix.trace ((σ x : GL n A) : Matrix n n A))
      = Matrix.trace ((Deformation.mapRepn n G 𝓞 f σ x : GL n B) : Matrix n n B) :=
        (Deformation.trace_mapRepn f σ x).symm
    _ = Matrix.trace ((((δ : ConjAct (GL n B)) • Deformation.mapRepn n G 𝓞 g σ) x : GL n B) : Matrix n n B) := by
        rw [hδ']
    _ = Matrix.trace ((Deformation.mapRepn n G 𝓞 g σ x : GL n B) : Matrix n n B) :=
        Deformation.trace_smul_eq (δ : ConjAct (GL n B)) (Deformation.mapRepn n G 𝓞 g σ) x
    _ = g.hom (Matrix.trace ((σ x : GL n A) : Matrix n n A)) := Deformation.trace_mapRepn g σ x
