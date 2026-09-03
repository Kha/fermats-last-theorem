import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCechCup
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCochainPullback
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCechOrdered
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCechReversal
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_orev_ocup

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.OModulePresheaf.orev_ocup
    {R : Type u} [CommRing R] {V : Scheme.{u}} (π : V ⟶ Spec (CommRingCat.of R))
    (K : V.OrderedAffineCover) (a b n : ℕ) (hn : a + b = n)
    (α : (OModulePresheaf.unit π).ocochain K a) (β : (OModulePresheaf.unit π).ocochain K b) :
    (OModulePresheaf.unit π).orev K n ((OModulePresheaf.unit π).ocup K a b n hn α β) =
      ((-1 : ℤ) ^ (a * b)) • (OModulePresheaf.unit π).ocup K b a n (by omega)
        ((OModulePresheaf.unit π).orev K b β) ((OModulePresheaf.unit π).orev K a α) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_orev_ocup.solution
