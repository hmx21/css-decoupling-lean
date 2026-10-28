import Decoupling.Syndrome
import Mathlib.LinearAlgebra.Quotient.Basic

/-! Exact syndrome quotients commute with restriction of scalars. -/

namespace Decoupling.ScalarRestriction

universe u

noncomputable section

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
  {P F Q : Type u}
  [AddCommGroup P] [Module B P] [Module A P] [IsScalarTower A B P]
  [AddCommGroup F] [Module B F] [Module A F] [IsScalarTower A B F]
  [AddCommGroup Q] [Module B Q] [Module A Q] [IsScalarTower A B Q]

variable (A) (c : Syndrome.Cochain B P F Q)

def restricted : Syndrome.Cochain A P F Q where
  d₁ := c.d₁.restrictScalars A
  γ := c.γ.restrictScalars A
  square := by
    ext p
    exact DFunLike.congr_fun c.square p

/-- Identical quotient relations, with the actual restricted scalar action. -/
def NEquiv : (restricted A c).N ≃ₗ[A] c.N where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def LEquiv : (restricted A c).L ≃ₗ[A] c.L where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def C1Equiv : (restricted A c).C1 ≃ₗ[A] c.C1 where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def C2Equiv : (restricted A c).C2 ≃ₗ[A] c.C2 where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem NEquiv_ε (v : F) : NEquiv A c ((restricted A c).ε v) = c.ε v := rfl
theorem LEquiv_π (v : (restricted A c).N) :
    LEquiv A c ((restricted A c).π v) = c.π (NEquiv A c v) := rfl
theorem NEquiv_ι (v : (restricted A c).C1) :
    NEquiv A c ((restricted A c).ι v) = c.ι (C1Equiv A c v) := rfl
theorem C2Equiv_pQ (v : Q) : C2Equiv A c ((restricted A c).pQ v) = c.pQ v := rfl

end
end Decoupling.ScalarRestriction
