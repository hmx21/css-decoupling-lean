import Mathlib.RingTheory.MvPolynomial.Groebner
import Mathlib.Data.Finsupp.PWO
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# HD014 polynomial modules and their actual monomial coefficients

The carrier is the ordinary finite free module over the D-variable
polynomial ring. No Gröbner, exactness or freeness conclusion is assumed.
This module is mathematical infrastructure, not an executable Gröbner program.
-/
namespace Decoupling.HighDim.SchreyerModule
noncomputable section
open MvPolynomial

abbrev Poly (K : Type*) [CommSemiring K] (D : ℕ) := MvPolynomial (Fin D) K
abbrev Vec (K : Type*) [CommSemiring K] (D r : ℕ) := Fin r → Poly K D
abbrev Exponent (D : ℕ) := Fin D →₀ ℕ
abbrev Term (D r : ℕ) := Exponent D × Fin r

def shift {D r : ℕ} (a : Exponent D) (t : Term D r) : Term D r := (a+t.1,t.2)

@[simp] theorem shift_zero {D r : ℕ} (t : Term D r) : shift 0 t=t := by cases t; simp [shift]
@[simp] theorem shift_add {D r : ℕ} (a b : Exponent D) (t : Term D r) :
    shift (a+b) t=shift a (shift b t) := by simp [shift,add_assoc]

def Divides {D r : ℕ} (s t : Term D r) : Prop := s.2=t.2 ∧ s.1≤t.1

theorem divides_refl {D r : ℕ} (t : Term D r) : Divides t t := ⟨rfl,le_rfl⟩
theorem divides_trans {D r : ℕ} {s t u : Term D r} (h : Divides s t) (g : Divides t u) :
    Divides s u := ⟨h.1.trans g.1,h.2.trans g.2⟩
theorem divides_iff_shift {D r : ℕ} (s t : Term D r) :
    Divides s t ↔ ∃ a : Exponent D, shift a s=t := by
  constructor
  · intro h
    refine ⟨t.1-s.1,Prod.ext ?_ h.1⟩
    exact tsub_add_cancel_of_le h.2
  · rintro ⟨a,rfl⟩
    exact ⟨rfl,le_add_left le_rfl⟩

variable {K : Type*} [CommRing K] {D r : ℕ}

def coeff (f : Vec K D r) (t : Term D r) : K := (f t.2).coeff t.1

def monomial (t : Term D r) (a : K) : Vec K D r := Pi.single t.2 (MvPolynomial.monomial t.1 a)

def support (f : Vec K D r) : Finset (Term D r) :=
  Finset.univ.biUnion (fun i => (f i).support.image (fun a => (a,i)))

@[simp] theorem mem_support (f : Vec K D r) (t : Term D r) :
    t ∈ support f ↔ coeff f t ≠ 0 := by
  classical
  rcases t with ⟨a,i⟩
  simp [support,coeff,Prod.mk.injEq]

@[ext] theorem ext {f g : Vec K D r} (h : ∀ t, coeff f t=coeff g t) : f=g := by
  funext i
  ext a
  exact h (a,i)

@[simp] theorem coeff_zero (t : Term D r) : coeff (0 : Vec K D r) t=0 := by simp [coeff]
@[simp] theorem coeff_add (f g : Vec K D r) (t : Term D r) :
    coeff (f+g) t=coeff f t+coeff g t := by simp [coeff]
@[simp] theorem coeff_neg (f : Vec K D r) (t : Term D r) : coeff (-f) t= -coeff f t := by simp [coeff]
@[simp] theorem coeff_sub (f g : Vec K D r) (t : Term D r) :
    coeff (f-g) t=coeff f t-coeff g t := by simp [coeff]

@[simp] theorem coeff_monomial (s t : Term D r) (a : K) :
    coeff (monomial s a) t = if s=t then a else 0 := by
  classical
  rcases s with ⟨b,i⟩
  rcases t with ⟨c,j⟩
  by_cases hij : i=j
  · subst j
    simp [coeff,monomial,MvPolynomial.coeff_monomial]
  · simp [coeff,monomial,hij,Ne.symm hij,Prod.mk.injEq]

@[simp] theorem monomial_zero (t : Term D r) : monomial t (0 : K)=0 := by
  apply ext
  intro u
  simp

theorem monomial_smul_monomial (a : Exponent D) (c b : K) (t : Term D r) :
    (MvPolynomial.monomial a c : Poly K D) • monomial t b = monomial (shift a t) (c*b) := by
  classical
  funext i
  by_cases hi : i=t.2
  · subst i
    simp [monomial,shift,Pi.smul_apply,smul_eq_mul,MvPolynomial.monomial_mul_monomial]
  · simp [monomial,shift,Pi.smul_apply,hi]

@[simp] theorem support_zero : support (0 : Vec K D r)=∅ := by
  ext t
  simp

theorem support_nonempty_iff (f : Vec K D r) : (support f).Nonempty ↔ f≠0 := by
  constructor
  · rintro ⟨t,ht⟩ h
    simp [h] at ht
  · intro hf
    by_contra he
    apply hf
    apply ext
    intro t
    have ht : t ∉ support f := fun ht => he ⟨t,ht⟩
    simpa only [mem_support,not_not,coeff_zero] using ht

/-- Every coefficient vector is the finite sum of its actual monomials. -/
theorem sum_monomials (f : Vec K D r) :
    ∑ t ∈ support f, monomial t (coeff f t) = f := by
  classical
  apply ext
  intro u
  simp only [coeff,Finset.sum_apply,MvPolynomial.coeff_sum]
  change (∑ t ∈ support f, coeff (monomial t (coeff f t)) u) = coeff f u
  simp only [coeff_monomial]
  by_cases hu : u ∈ support f
  · simp [hu]
  · have hz : coeff f u=0 := by simpa only [mem_support,not_not] using hu
    simp [hu,hz]

end
end Decoupling.HighDim.SchreyerModule
