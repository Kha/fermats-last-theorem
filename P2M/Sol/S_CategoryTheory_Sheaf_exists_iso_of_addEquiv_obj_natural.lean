import Mathlib
import P2M.Util
namespace P2MW.S_CategoryTheory_Sheaf_exists_iso_of_addEquiv_obj_natural

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u

theorem solution
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (F G : Sheaf J Ab.{w}) (e : ∀ U : Cᵒᵖ, F.obj.obj U ≃+ G.obj.obj U)
    (he : ∀ {U V : Cᵒᵖ} (k : U ⟶ V) (s : F.obj.obj U), e V (F.obj.map k s) = G.obj.map k (e U s)) :
    ∃ φ : F ≅ G, ∀ (U : Cᵒᵖ) (s : F.obj.obj U), φ.hom.hom.app U s = e U s := by
  let α : F.obj ≅ G.obj := NatIso.ofComponents (fun U => (e U).toAddCommGrpIso) (by
    intro U V k
    ext s
    simpa using he k s)
  refine ⟨(sheafToPresheaf J Ab.{w}).preimageIso α, fun U s => ?_⟩
  have : ((sheafToPresheaf J Ab.{w}).preimageIso α).hom.hom = α.hom := by
    have h := (sheafToPresheaf J Ab.{w}).map_preimage α.hom
    simpa using h
  rw [this]
  rfl
