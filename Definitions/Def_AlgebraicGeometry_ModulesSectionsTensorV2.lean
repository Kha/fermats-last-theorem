import Mathlib
import Definitions.Def_PresheafOfModules_InternalHom
import Definitions.Def_SheafOfModules_MonoidalV2
import Definitions.Def_AlgebraicGeometry_ModulesTensorPowV2
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory MonoidalCategory Opposite TensorProduct

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

section Hom

variable (L M : X.Modules)

end Hom

section Sections

variable {L M : X.Modules} {U : X.Opens}

end Sections

section Pow

variable {L : X.Modules} {U : X.Opens}

end Pow

section Frame

variable {M : X.Modules} {U : X.Opens}

namespace IsFrameOn

variable {s : Γ(M, U)} {V : X.Opens}

end IsFrameOn

end Frame

end AlgebraicGeometry.Scheme.Modules

end
