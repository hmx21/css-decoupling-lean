import Decoupling.HighDim.SchreyerGroebnerDivision
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Order.OrderIsoNat
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Initial modules and the strict progress invariant of Buchberger completion

A nonzero reduced remainder contributes a genuinely new leading monomial.
Noetherianity rules out infinitely many such additions. This theorem is
an invariant/termination foundation, not a claim of an implemented runtime
Buchberger loop or its final correctness criterion.
-/
namespace Decoupling.HighDim.SchreyerModule
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {K : Type*} [Field K] {D r s : ℕ}

/-- Coefficients of a scalar multiple of a module monomial can only occur at divisible terms. -/
theorem coeff_smul_monomial_zero (q : Poly K D) (u t : Term D r) (c : K)
    (h : ¬Divides u t) : coeff (q • monomial u c) t=0 := by
  classical
  rcases u with ⟨a,i⟩
  rcases t with ⟨b,j⟩
  by_cases hij : i=j
  · subst j
    have hn : ¬a≤b := fun hab => h ⟨rfl,hab⟩
    simp only [coeff,monomial,Pi.smul_apply,Pi.single_eq_same,smul_eq_mul,
      MvPolynomial.coeff_mul_monomial',ite_eq_right hn]
  · simp [coeff,monomial,Ne.symm hij,Pi.smul_apply]

def initialTerms (o : ModuleOrder D r) (G : Fin s → Vec K D r) : Set (Vec K D r) :=
  {v | ∃ i t,IsLeading o (G i) t ∧ v=monomial t 1}

def initialSpan (o : ModuleOrder D r) (G : Fin s → Vec K D r) :
    Submodule (Poly K D) (Vec K D r) := Submodule.span (Poly K D) (initialTerms o G)

/-- Exact monomial membership, including ambient zero coordinates. -/
theorem monomial_mem_initialSpan_iff (o : ModuleOrder D r) (G : Fin s → Vec K D r) (t : Term D r) :
    monomial t (1 : K)∈initialSpan o G ↔ ∃ i u,IsLeading o (G i) u ∧ Divides u t := by
  classical
  constructor
  · intro hm
    by_contra hn
    have vanish (v : Vec K D r) (hv : v∈initialSpan o G) : ∀ q : Poly K D,coeff (q • v) t=0 := by
      induction hv using Submodule.span_induction with
      | mem v hv =>
        obtain ⟨i,u,hi,rfl⟩ := hv
        exact fun q => coeff_smul_monomial_zero q u t 1 (fun hd => hn ⟨i,u,hi,hd⟩)
      | zero => intro q; simp
      | add x y hx hy ihx ihy =>
        intro q
        rw [smul_add,coeff_add,ihx q,ihy q,add_zero]
      | smul a x hx ih =>
        intro q
        rw [smul_smul]
        exact ih (q*a)
    have hbad := vanish _ hm 1
    simp at hbad
  · rintro ⟨i,u,hi,hd⟩
    obtain ⟨a,ha⟩ := (divides_iff_shift u t).mp hd
    have hm : monomial u (1 : K)∈initialSpan o G := Submodule.subset_span ⟨i,u,hi,rfl⟩
    have hs := (initialSpan o G).smul_mem (MvPolynomial.monomial a (1 : K)) hm
    simpa only [monomial_smul_monomial,one_mul,ha] using hs

theorem initialSpan_mono_of_map {n : ℕ} (o : ModuleOrder D r)
    (G : Fin s → Vec K D r) (H : Fin n → Vec K D r)
    (j : Fin s → Fin n) (hj : ∀ i,H (j i)=G i) : initialSpan o G ≤ initialSpan o H := by
  apply Submodule.span_mono
  rintro v ⟨i,t,hi,rfl⟩
  exact ⟨j i,t,by rw [hj]; exact hi,rfl⟩

/-- Each nonzero normal-form insertion strictly enlarges the actual initial module. -/
theorem initialSpan_lt_snoc (o : ModuleOrder D r) (G : Fin s → Vec K D r)
    (rem : Vec K D r) (hr : rem≠0) (hred : Reduced o G rem) :
    initialSpan o G < initialSpan o (Fin.snoc G rem) := by
  classical
  have hle : initialSpan o G ≤ initialSpan o (Fin.snoc G rem) :=
    initialSpan_mono_of_map o G _ Fin.castSucc (fun i => Fin.snoc_castSucc _ _ i)
  apply lt_of_le_of_ne hle
  intro he
  have hnew : monomial (lm o rem hr) (1 : K)∈initialSpan o (Fin.snoc G rem) :=
    Submodule.subset_span ⟨Fin.last s,lm o rem hr,by simpa only [Fin.snoc_last] using lm_isLeading o rem hr,rfl⟩
  rw [←he] at hnew
  obtain ⟨i,u,hi,hd⟩ := (monomial_mem_initialSpan_iff o G _).mp hnew
  exact hred _ (lc_ne_zero o rem hr) i u hi hd

/-- Buchberger's additions cannot form an infinite strict ascending chain.
Zero-remainder queue steps require the separate finite-queue measure. -/
theorem no_infinite_initial_increases (o : ModuleOrder D r) (sizes : ℕ → ℕ)
    (G : ∀ n,Fin (sizes n) → Vec K D r)
    (hg : ∀ n,initialSpan o (G n) < initialSpan o (G (n+1))) : False := by
  let : IsNoetherianRing (Poly K D) := inferInstance
  let : IsNoetherian (Poly K D) (Vec K D r) := inferInstance
  have hmono : StrictMono (fun n => initialSpan o (G n)) := strictMono_nat_of_lt_succ hg
  exact not_strictMono_of_wellFoundedGT _ hmono

/-- Adjoining an actual relation already in the span preserves that span. -/
theorem span_snoc_eq (G : Fin s → Vec K D r) (rem : Vec K D r)
    (hr : rem∈Submodule.span (Poly K D) (Set.range G)) :
    Submodule.span (Poly K D) (Set.range (Fin.snoc G rem)) = Submodule.span (Poly K D) (Set.range G) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    induction i using Fin.lastCases with
    | last =>
      rw [Fin.snoc_last]
      exact hr
    | cast i => exact Submodule.subset_span ⟨i,by simp⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    exact Submodule.subset_span ⟨i.castSucc,by simp⟩

end
end Decoupling.HighDim.SchreyerModule
