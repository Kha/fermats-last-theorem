import Definitions.Def_NumberField_AdelicHaar
import P2M.Util
import P2M.Sol.S_NumberField_AdelicHaar_isMulRightInvariant_adelicGLHaar

set_option autoImplicit false

open scoped NumberField

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem NumberField.AdelicHaar.isMulRightInvariant_adelicGLHaar (F : Type) [Field F] [NumberField F] :
    (adelicGLHaar (Fin 2) (𝓞 F) F).IsMulRightInvariant := by p2m_exact_reverting @_root_.P2MW.S_NumberField_AdelicHaar_isMulRightInvariant_adelicGLHaar.solution
