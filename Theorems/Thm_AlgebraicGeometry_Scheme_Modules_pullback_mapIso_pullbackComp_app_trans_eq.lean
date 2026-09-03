import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_pullback_mapIso_pullbackComp_app_trans_eq

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

theorem AlgebraicGeometry.Scheme.Modules.pullback_mapIso_pullbackComp_app_trans_eq
    {T₃ T₂ T₁ X₃ A'' A' : Scheme.{u}} (e₃ : T₃ ⟶ X₃) (b : X₃ ⟶ A'') (s : T₃ ⟶ T₂) (e'' : T₂ ⟶ A'')
    (a : A'' ⟶ A') (i : T₂ ⟶ T₁) (e' : T₁ ⟶ A') (hb : e₃ ≫ b = s ≫ e'') (ha : e'' ≫ a = i ≫ e')
    (hk : e₃ ≫ b ≫ a = (s ≫ i) ≫ e') (L : A'.Modules) :
    (Scheme.Modules.pullback e₃).mapIso ((Scheme.Modules.pullbackComp b a).app L) ≪≫
        ((Scheme.Modules.pullbackComp e₃ (b ≫ a)).app L ≪≫ (Scheme.Modules.pullbackCongr hk).app L ≪≫
          ((Scheme.Modules.pullbackComp (s ≫ i) e').app L).symm) =
      ((Scheme.Modules.pullbackComp e₃ b).app ((Scheme.Modules.pullback a).obj L) ≪≫
          (Scheme.Modules.pullbackCongr hb).app ((Scheme.Modules.pullback a).obj L) ≪≫
          ((Scheme.Modules.pullbackComp s e'').app ((Scheme.Modules.pullback a).obj L)).symm) ≪≫
        (Scheme.Modules.pullback s).mapIso
          ((Scheme.Modules.pullbackComp e'' a).app L ≪≫ (Scheme.Modules.pullbackCongr ha).app L ≪≫
            ((Scheme.Modules.pullbackComp i e').app L).symm) ≪≫
        (Scheme.Modules.pullbackComp s i).app ((Scheme.Modules.pullback e').obj L) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_pullback_mapIso_pullbackComp_app_trans_eq.solution
