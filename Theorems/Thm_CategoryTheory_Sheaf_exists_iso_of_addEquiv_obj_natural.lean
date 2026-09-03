import Mathlib
import P2M.Util
import P2M.Sol.S_CategoryTheory_Sheaf_exists_iso_of_addEquiv_obj_natural

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u

theorem CategoryTheory.Sheaf.exists_iso_of_addEquiv_obj_natural
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (F G : Sheaf J Ab.{w}) (e : ∀ U : Cᵒᵖ, F.obj.obj U ≃+ G.obj.obj U)
    (he : ∀ {U V : Cᵒᵖ} (k : U ⟶ V) (s : F.obj.obj U), e V (F.obj.map k s) = G.obj.map k (e U s)) :
    ∃ φ : F ≅ G, ∀ (U : Cᵒᵖ) (s : F.obj.obj U), φ.hom.hom.app U s = e U s := by p2m_exact_reverting @_root_.P2MW.S_CategoryTheory_Sheaf_exists_iso_of_addEquiv_obj_natural.solution
