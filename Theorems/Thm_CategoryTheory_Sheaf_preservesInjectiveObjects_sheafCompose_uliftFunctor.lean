import Mathlib
import P2M.Util
import P2M.Sol.S_CategoryTheory_Sheaf_preservesInjectiveObjects_sheafCompose_uliftFunctor

set_option autoImplicit false

open CategoryTheory

universe u

theorem CategoryTheory.Sheaf.preservesInjectiveObjects_sheafCompose_uliftFunctor
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C) :
    (sheafCompose J AddCommGrpCat.uliftFunctor.{u+1, u} :
      Sheaf J AddCommGrpCat.{u} ⥤ Sheaf J AddCommGrpCat.{u+1}).PreservesInjectiveObjects := by p2m_exact_reverting @_root_.P2MW.S_CategoryTheory_Sheaf_preservesInjectiveObjects_sheafCompose_uliftFunctor.solution
