import Flypitch.BVMExtras
import Flypitch.PSetOrdinal

universe u

namespace Flypitch

open Cardinal

/-!
`Flypitch.AlephOne` starts the forcing-side `aleph_one.lean` port. This first tranche keeps to the
pure `pSet` layer built on top of `Flypitch.PSetOrdinal`: regularity, the canonical `aleph_one`
pre-set, set-theoretic complement/intersection, and the basic ordinal-style comparison lemmas for
ordinal-shaped pre-sets.
-/

set_option linter.missingDocs false
set_option linter.style.longLine false

namespace pSet

/-- Every nonempty pre-set has an `∈`-minimal member. -/
theorem regularity (x : pSet.{u}) (hNonempty : ¬ PSet.Equiv x (∅ : pSet.{u})) :
    ∃ y : pSet.{u}, y ∈ x ∧ ∀ z, z ∈ x → z ∉ y := by
  classical
  have hxMem : ∃ y : pSet.{u}, y ∈ x := by
    by_contra hNo
    apply hNonempty
    apply (ext_iff).2
    intro z
    constructor
    · intro hz
      exact False.elim (hNo ⟨z, hz⟩)
    · intro hz
      exact False.elim (PSet.notMem_empty _ hz)
  have hxNonempty : x.Nonempty := by
    simpa [PSet.nonempty_def] using hxMem
  simpa using well_founded x hxNonempty

/-- The pre-set coding `aleph_1`. -/
noncomputable def aleph_one : pSet.{u} :=
  card_ex (Cardinal.aleph 1)

theorem aleph_one_Ord : Ord aleph_one := by
  simpa [aleph_one, card_ex] using Ord_mk (Cardinal.ord (Cardinal.aleph 1))

/-- The pre-set coding `aleph_2`. -/
noncomputable def aleph_two : pSet.{u} :=
  card_ex (Cardinal.aleph 2)

theorem aleph_two_Ord : Ord aleph_two := by
  simpa [aleph_two, card_ex] using Ord_mk (Cardinal.ord (Cardinal.aleph 2))

/-- A weak characterization of `aleph_one`: an ordinal admitting no injection into `omega` and
contained in every other such ordinal. -/
def aleph_one_weak_Ord_spec (x : pSet.{u}) : Prop :=
  Ord x ∧ ∀ y : pSet.{u}, Ord y ∧ ¬ injects_into y (PSet.omega : pSet.{u}) → x ⊆ y

/-- The trichotomy relation on members of a pre-set. -/
def epsilon_trichotomy (x : pSet.{u}) : Prop :=
  ∀ y : pSet.{u}, y ∈ x → ∀ z : pSet.{u}, z ∈ x → PSet.Equiv y z ∨ y ∈ z ∨ z ∈ y

theorem epsilon_trichotomy_of_Ord {x : pSet.{u}} (hOrd : Ord x) : epsilon_trichotomy x :=
  hOrd.1.1

theorem epsilon_trichotomy_of_Ord' {x : pSet.{u}} (hOrd : Ord x) {y : pSet.{u}} (hy : y ∈ x)
    {z : pSet.{u}} (hz : z ∈ x) : PSet.Equiv y z ∨ y ∈ z ∨ z ∈ y :=
  epsilon_trichotomy_of_Ord hOrd y hy z hz

theorem is_transitive_of_mem_Ord {x : pSet.{u}} (hOrd : Ord x) : is_transitive x :=
  is_transitive_of_Ord hOrd

theorem mem_of_mem_subset {x y z : pSet.{u}} (hSub : y ⊆ z) (hMem : x ∈ y) : x ∈ z :=
  all_mem_of_subset hSub x hMem

theorem mem_of_mem_Ord {x y z : pSet.{u}} (hOrd : Ord z) (hMem₁ : x ∈ y) (hMem₂ : y ∈ z) :
    x ∈ z :=
  mem_trans_of_transitive hMem₁ hMem₂ (is_transitive_of_Ord hOrd)

theorem subset_of_mem_Ord {x z : pSet.{u}} (hOrd : Ord z) (hMem : x ∈ z) : x ⊆ z :=
  is_transitive_of_Ord hOrd x hMem

theorem Ord_of_mem_Ord {x z : pSet.{u}} (hMem : x ∈ z) (hOrd : Ord z) : Ord x := by
  refine ⟨?_, transitive_of_mem_Ord hOrd hMem⟩
  constructor
  · intro y hy z' hz
    exact epsilon_trichotomy_of_Ord' hOrd
      (mem_of_mem_Ord hOrd hy hMem)
      (mem_of_mem_Ord hOrd hz hMem)
  · intro s _ hs
    exact well_founded s hs

/-- Relative complement inside a pre-set. -/
def compl (x y : pSet.{u}) : pSet.{u} :=
  PSet.sep (fun z => ¬ z ∈ y) x

theorem mem_compl_iff {x y z : pSet.{u}} : z ∈ compl x y ↔ z ∈ x ∧ ¬ z ∈ y := by
  simpa [compl] using
    (mem_sep_iff (x := x) (w := z) (p := fun w => ¬ w ∈ y)
      (hcongr := P_ext_neg (P_ext_mem_left (y := y))))

/-- Nonemptiness expressed as non-equivalence with the empty pre-set. -/
@[reducible] def non_empty (x : pSet.{u}) : Prop :=
  ¬ PSet.Equiv x (∅ : pSet.{u})

theorem equiv_unfold' {x y : pSet.{u}} :
    PSet.Equiv x y ↔ (∀ z, z ∈ x → z ∈ y) ∧ ∀ z, z ∈ y → z ∈ x := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro z hz
      exact (PSet.Mem.congr_right h).1 hz
    · intro z hz
      exact (PSet.Mem.congr_right h).2 hz
  · rintro ⟨hxy, hyx⟩
    exact (ext_iff).2 fun z => ⟨hxy z, hyx z⟩

theorem nonempty_iff_exists_mem {x : pSet.{u}} : non_empty x ↔ ∃ y : pSet.{u}, y ∈ x := by
  classical
  constructor
  · intro hx
    by_contra hNo
    apply hx
    apply (ext_iff).2
    intro z
    constructor
    · intro hz
      exact False.elim (hNo ⟨z, hz⟩)
    · intro hz
      exact False.elim (PSet.notMem_empty _ hz)
  · rintro ⟨y, hy⟩ hEq
    exact PSet.notMem_empty _ ((PSet.Mem.congr_right hEq).1 hy)

theorem nonempty_compl_of_ne {x y : pSet.{u}} (hNe : ¬ PSet.Equiv x y) :
    non_empty (compl x y) ∨ non_empty (compl y x) := by
  classical
  by_cases hxy : ∃ z : pSet.{u}, z ∈ x ∧ ¬ z ∈ y
  · left
    rw [nonempty_iff_exists_mem]
    rcases hxy with ⟨z, hz₁, hz₂⟩
    exact ⟨z, (mem_compl_iff).2 ⟨hz₁, hz₂⟩⟩
  · right
    rw [nonempty_iff_exists_mem]
    by_contra hNo
    apply hNe
    apply (ext_iff).2
    intro z
    constructor
    · intro hz
      by_contra hzNot
      exact hxy ⟨z, hz, hzNot⟩
    · intro hz
      by_contra hzNot
      exact hNo ⟨z, (mem_compl_iff).2 ⟨hz, hzNot⟩⟩

theorem compl_empty_of_subset {x y : pSet.{u}} (hSub : x ⊆ y) :
    PSet.Equiv (compl x y) (∅ : pSet.{u}) := by
  classical
  by_contra hContra
  change non_empty (compl x y) at hContra
  rcases (nonempty_iff_exists_mem).1 hContra with ⟨z, hz⟩
  rcases (mem_compl_iff).1 hz with ⟨hzx, hznoty⟩
  exact hznoty (mem_of_mem_subset hSub hzx)

/-- Binary intersection of pre-sets. -/
def binary_inter (x y : pSet.{u}) : pSet.{u} :=
  PSet.sep (fun z => z ∈ y) x

theorem mem_binary_inter_iff {x y z : pSet.{u}} :
    z ∈ binary_inter x y ↔ z ∈ x ∧ z ∈ y := by
  simpa [binary_inter] using
    (mem_sep_iff (x := x) (w := z) (p := fun w => w ∈ y)
      (hcongr := P_ext_mem_left (y := y)))

theorem binary_inter_subset {x y : pSet.{u}} :
    binary_inter x y ⊆ x ∧ binary_inter x y ⊆ y := by
  refine ⟨sep_subset (p := fun z => z ∈ y) (x := x), ?_⟩
  exact subset_of_all_mem fun z hz => (mem_binary_inter_iff).1 hz |>.2

theorem Ord_binary_inter {x y : pSet.{u}} (h₁ : Ord x) (h₂ : Ord y) :
    Ord (binary_inter x y) := by
  refine ⟨?_, ?_⟩
  · constructor
    · intro w hw z hz
      exact epsilon_trichotomy_of_Ord' h₁
        ((mem_binary_inter_iff).1 hw).1
        ((mem_binary_inter_iff).1 hz).1
    · intro s _ hs
      exact well_founded s hs
  · intro z hz
    rcases (mem_binary_inter_iff).1 hz with ⟨hzx, hzy⟩
    apply subset_of_all_mem
    intro w hw
    refine (mem_binary_inter_iff).2 ⟨?_, ?_⟩
    · exact mem_of_mem_Ord h₁ hw hzx
    · exact mem_of_mem_Ord h₂ hw hzy

theorem Ord.lt_of_ne_and_le {x y : pSet.{u}} (h₁ : Ord x) (h₂ : Ord y)
    (hNe : ¬ PSet.Equiv x y) (hLe : x ⊆ y) : x ∈ y := by
  classical
  have hComplNonempty : non_empty (compl y x) := by
    rcases nonempty_compl_of_ne hNe with hxy | hyx
    · exfalso
      exact hxy (compl_empty_of_subset hLe)
    · exact hyx
  rcases regularity (compl y x) hComplNonempty with ⟨z, hz, hzMin⟩
  rcases (mem_compl_iff).1 hz with ⟨hzY, hzNotX⟩
  have hEq : PSet.Equiv x z := by
    apply (ext_iff).2
    intro a
    constructor
    · intro haX
      have haY : a ∈ y := mem_of_mem_subset hLe haX
      rcases epsilon_trichotomy_of_Ord' h₂ haY hzY with hEq' | haZ | hzA
      · exact False.elim (hzNotX ((PSet.Mem.congr_left hEq').1 haX))
      · exact haZ
      · exact False.elim (hzNotX (mem_of_mem_Ord h₁ hzA haX))
    · intro haZ
      by_contra haNotX
      have haY : a ∈ y := mem_of_mem_Ord h₂ haZ hzY
      have haCompl : a ∈ compl y x := (mem_compl_iff).2 ⟨haY, haNotX⟩
      exact hzMin a haCompl haZ
  exact (PSet.Mem.congr_left hEq).2 hzY

theorem Ord.le_or_le {x y : pSet.{u}} (h₁ : Ord x) (h₂ : Ord y) : x ⊆ y ∨ y ⊆ x := by
  classical
  let w : pSet.{u} := binary_inter x y
  have hwOrd : Ord w := Ord_binary_inter h₁ h₂
  have hwEq : PSet.Equiv w x ∨ PSet.Equiv w y := by
    by_contra h
    have h' := not_or.mp h
    have hwx : w ∈ x := Ord.lt_of_ne_and_le hwOrd h₁ h'.1 (binary_inter_subset (x := x) (y := y)).1
    have hwy : w ∈ y := Ord.lt_of_ne_and_le hwOrd h₂ h'.2 (binary_inter_subset (x := x) (y := y)).2
    have hww : w ∈ w := (mem_binary_inter_iff).2 ⟨hwx, hwy⟩
    exact mem_self hww
  rcases hwEq with hEq | hEq
  · left
    exact (PSet.Subset.congr_left hEq).1 (binary_inter_subset (x := x) (y := y)).2
  · right
    exact (PSet.Subset.congr_left hEq).1 (binary_inter_subset (x := x) (y := y)).1

theorem equiv.comm {x y : pSet.{u}} : PSet.Equiv x y ↔ PSet.Equiv y x := by
  constructor <;> intro h <;> exact h.symm

theorem Ord.trichotomy {x y : pSet.{u}} (h₁ : Ord x) (h₂ : Ord y) :
    PSet.Equiv x y ∨ x ∈ y ∨ y ∈ x := by
  classical
  rcases Ord.le_or_le h₁ h₂ with hxy | hyx
  · by_cases hEq : PSet.Equiv x y
    · exact Or.inl hEq
    · exact Or.inr (Or.inl (Ord.lt_of_ne_and_le h₁ h₂ hEq hxy))
  · by_cases hEq : PSet.Equiv x y
    · exact Or.inl hEq
    · exact Or.inr (Or.inr (Ord.lt_of_ne_and_le h₂ h₁
        (by simpa [equiv.comm] using hEq) hyx))

theorem Ord.lt_of_le_of_lt {x y z : pSet.{u}} (hx : Ord x) (hy : Ord y) (hz : Ord z)
    (hLe : x ⊆ y) (hLt : y ∈ z) : x ∈ z := by
  rcases Ord.trichotomy hx hy with hEq | hxy | hyx
  · exact (PSet.Mem.congr_left hEq).2 hLt
  · exact mem_trans_of_transitive hxy hLt (is_transitive_of_Ord hz)
  · have hySub : y ⊆ x := subset_of_mem_Ord hx hyx
    have hEq' : PSet.Equiv x y := by
      apply (ext_iff).2
      intro a
      exact ⟨fun ha => all_mem_of_subset hLe a ha, fun ha => all_mem_of_subset hySub a ha⟩
    exact (PSet.Mem.congr_left hEq').2 hLt

theorem Ord.le_iff_lt_or_eq {x z : pSet.{u}} (h₁ : Ord x) (h₂ : Ord z) :
    x ⊆ z ↔ x ∈ z ∨ PSet.Equiv x z := by
  constructor
  · intro hLe
    by_cases hEq : PSet.Equiv x z
    · exact Or.inr hEq
    · exact Or.inl (Ord.lt_of_ne_and_le h₁ h₂ hEq hLe)
  · rintro (hLt | hEq)
    · exact subset_of_mem_Ord h₂ hLt
    · exact subset_of_all_mem fun a ha => (PSet.Mem.congr_right hEq).1 ha

/-- The ordinal coded by an element of `ordinal.mk η`, obtained from the witnessing equivalence. -/
noncomputable def ordOfMemMk {η : ordinal} (i : (ordinal.mk η).Type) : ordinal :=
  Classical.choose
    (equiv_mk_of_mem_mk (η := η) (x := (ordinal.mk η).Func i)
      (mem_mk' (x := ordinal.mk η) (i := i)))

theorem ordOfMemMk_lt {η : ordinal} (i : (ordinal.mk η).Type) : ordOfMemMk i < η :=
  (Classical.choose_spec
    (equiv_mk_of_mem_mk (η := η) (x := (ordinal.mk η).Func i)
      (mem_mk' (x := ordinal.mk η) (i := i)))).1

theorem func_equiv_ordOfMemMk {η : ordinal} (i : (ordinal.mk η).Type) :
    PSet.Equiv ((ordinal.mk η).Func i) (ordinal.mk (ordOfMemMk i)) :=
  (Classical.choose_spec
    (equiv_mk_of_mem_mk (η := η) (x := (ordinal.mk η).Func i)
      (mem_mk' (x := ordinal.mk η) (i := i)))).2

theorem rank_func_eq_ordOfMemMk {η : ordinal} (i : (ordinal.mk η).Type) :
    PSet.rank ((ordinal.mk η).Func i) = ordOfMemMk i := by
  simpa [ordinal.mk] using PSet.rank_congr (func_equiv_ordOfMemMk i)

theorem ordOfMemMk_eq_of_equiv {η : ordinal} {i j : (ordinal.mk η).Type}
    (hEqv : PSet.Equiv ((ordinal.mk η).Func i) ((ordinal.mk η).Func j)) :
    ordOfMemMk i = ordOfMemMk j := by
  exact ordinal.mk_inj
    ((func_equiv_ordOfMemMk i).symm.trans (hEqv.trans (func_equiv_ordOfMemMk j)))

/-- Reinterpret the indexing type of `ordinal.mk η` as `η.ToType`. -/
abbrev mkTypeEquiv (η : ordinal) : (ordinal.mk η).Type ≃ η.ToType := by
  simpa [ordinal.mk] using Equiv.refl (η.ToType)

theorem mkToTypeEquivPSet {η : ordinal} :
    PSet.Equiv (PSet.mk η.ToType (fun a => ordinal.mk (a : ordinal))) (ordinal.mk η) := by
  apply (ext_iff).2
  intro z
  constructor
  · intro hz
    rcases mem_unfold.mp hz with ⟨a, hza⟩
    change η.ToType at a
    rw [ordinal.mk, Ordinal.mem_toPSet_iff]
    refine ⟨(a : ordinal), ?_, ?_⟩
    · exact (a : Set.Iio η).2
    · simpa using hza
  · intro hz
    rcases equiv_mk_of_mem_mk hz with ⟨ρ, hρη, hzρ⟩
    refine mem_unfold.mpr ?_
    refine ⟨(Ordinal.ToType.mk ⟨ρ, hρη⟩ : η.ToType), ?_⟩
    simpa [ordinal.mk] using hzρ

theorem mk_injects_into_of_mk_le_omega {η : ordinal}
    (hLe : Cardinal.mk (ordinal.mk η).Type ≤ Cardinal.mk (PSet.omega : pSet.{u}).Type) :
    injects_into (ordinal.mk η) PSet.omega := by
  have hCount : Countable η.ToType := by
    rw [← Ordinal.type_toPSet]
    rw [mk_omega_eq] at hLe
    exact Cardinal.mk_le_aleph0_iff.mp hLe
  let e : η.ToType → Nat := Classical.choose (Countable.exists_injective_nat η.ToType)
  have he : Function.Injective e := Classical.choose_spec (Countable.exists_injective_nat η.ToType)
  let code : (ordinal.mk η).Type → η.ToType :=
    fun i => Ordinal.ToType.mk ⟨ordOfMemMk i, ordOfMemMk_lt i⟩
  refine ⟨pSet.function.mk (fun i => PSet.omega.Func (ULift.up (e (code i)))), ?_⟩
  refine pSet.function.mk_is_injective_function
    (fun i => PSet.omega.Func (ULift.up (e (code i))))
    (fun i => mem_mk' (x := PSet.omega) (i := ULift.up (e (code i))))
    ?_ ?_
  · intro i j hEqv
    have hOrd : ordOfMemMk i = ordOfMemMk j := by
      exact ordinal.mk_inj
        ((func_equiv_ordOfMemMk i).symm.trans (hEqv.trans (func_equiv_ordOfMemMk j)))
    have hCodeIio : Ordinal.ToType.mk.symm (code i) = Ordinal.ToType.mk.symm (code j) := by
      simpa [code] using hOrd
    have hCode : code i = code j := Ordinal.ToType.mk.symm.injective hCodeIio
    have hCodeNat : e (code i) = e (code j) := congrArg e hCode
    simpa [hCodeNat] using
      (PSet.Equiv.rfl :
        PSet.Equiv (PSet.omega.Func (ULift.up (e (code j))))
          (PSet.omega.Func (ULift.up (e (code j)))))
  · intro i₁ i₂ hEqv
    have hCodeULift : ULift.up (e (code i₁)) = ULift.up (e (code i₂)) := omega_inj hEqv
    have hCodeNat : e (code i₁) = e (code i₂) := by
      simpa using hCodeULift
    have hCode : code i₁ = code i₂ := he hCodeNat
    have hOrd : ordOfMemMk i₁ = ordOfMemMk i₂ := by
      simpa [code] using congrArg (fun x : η.ToType => (x : ordinal)) hCode
    exact (func_equiv_ordOfMemMk i₁).trans
      ((mk_equiv_of_eq hOrd).trans (func_equiv_ordOfMemMk i₂).symm)

theorem injects_into_omega_of_mem_aleph_one {z : pSet} (hMem : z ∈ aleph_one) :
    injects_into z PSet.omega := by
  rcases equiv_mk_of_mem_mk hMem with ⟨w, hwlt, hzEq⟩
  have hInj : injects_into (ordinal.mk w) PSet.omega := by
    apply mk_injects_into_of_mk_le_omega
    rw [ordinal.mk_card, mk_omega_eq, Cardinal.card_le_iff]
    rw [aleph_one_eq_succ_aleph_zero] at hwlt
    exact hwlt
  exact (injects_into_congr_left hzEq.symm).1 hInj

theorem mk_le_omega_of_injects_into {η : ordinal}
    (h : injects_into (ordinal.mk η) PSet.omega) : Cardinal.mk (ordinal.mk η).Type ≤ cardinal.omega := by
  rcases h with ⟨f, hfFunc, hfInj⟩
  have hfFunc' : is_func (PSet.mk η.ToType (fun a => ordinal.mk (a : ordinal))) PSet.omega f :=
    (is_func_congr_left (mkToTypeEquivPSet (η := η))).mpr hfFunc
  let e : η.ToType → PSet.omega.Type := function_lift_indexed hfFunc'.2
  have he : Function.Injective e := by
    intro a₁ a₂ hEq
    have hEqv : PSet.Equiv (ordinal.mk (a₁ : ordinal)) (ordinal.mk (a₂ : ordinal)) :=
      equiv_of_function_lift_indexed_eq hfFunc' hfInj hEq
    apply Ordinal.ToType.mk.symm.injective
    apply Subtype.ext
    exact ordinal.mk_inj hEqv
  have hxy : Cardinal.mk η.ToType ≤ Cardinal.mk PSet.omega.Type := Cardinal.mk_le_of_injective he
  simpa [Ordinal.type_toPSet, mk_omega_eq] using hxy

theorem aleph_one_not_injects_into_omega : ¬ injects_into aleph_one PSet.omega := by
  intro hInj
  have hLe : Cardinal.mk aleph_one.Type ≤ cardinal.omega := mk_le_omega_of_injects_into hInj
  have hLt : cardinal.omega < Cardinal.mk aleph_one.Type := by
    rw [show Cardinal.mk aleph_one.Type = Cardinal.aleph 1 by simp [aleph_one, pSet.card_ex]]
    exact omega_lt_aleph_one
  exact not_le_of_gt hLt hLe

theorem empty_satisfies_weak_spec : aleph_one_weak_Ord_spec (∅ : pSet.{u}) := by
  refine ⟨?_, ?_⟩
  · simpa using (Ord_mk (0 : ordinal))
  · intro y hy
    exact subset_of_all_mem (fun z hz => False.elim (PSet.notMem_empty _ hz))

theorem aleph_one_satisfies_spec : aleph_one_weak_Ord_spec aleph_one := by
  refine ⟨aleph_one_Ord, ?_⟩
  intro z hz
  rcases hz with ⟨hzOrd, hzNotOmega⟩
  rcases Ord.trichotomy aleph_one_Ord hzOrd with hEq | hLt | hLt
  · exact (PSet.Subset.congr_left hEq).2 subset_refl
  · exact subset_of_mem_Ord hzOrd hLt
  · exact False.elim (hzNotOmega (injects_into_omega_of_mem_aleph_one hLt))

theorem equiv_aleph_one_of_weak_spec_of_not_injects_into_omega {x : pSet.{u}}
    (hx : aleph_one_weak_Ord_spec x) (hxNo : ¬ injects_into x PSet.omega) :
    PSet.Equiv x (aleph_one : pSet.{u}) := by
  rcases hx with ⟨hxOrd, hxMin⟩
  have hxSub : x ⊆ aleph_one := by
    exact hxMin aleph_one ⟨aleph_one_Ord, aleph_one_not_injects_into_omega⟩
  have haSub : aleph_one ⊆ x := by
    exact aleph_one_satisfies_spec.2 x ⟨hxOrd, hxNo⟩
  exact (ext_iff (x := x) (y := (aleph_one : pSet.{u}))).2 <| by
    intro z
    constructor
    · intro hz
      exact all_mem_of_subset hxSub z hz
    · intro hz
      exact all_mem_of_subset haSub z hz

theorem equiv_aleph_one_of_weak_spec {x : pSet.{u}} (hx : aleph_one_weak_Ord_spec x) :
    ¬ injects_into x PSet.omega → PSet.Equiv x (aleph_one : pSet.{u}) :=
  equiv_aleph_one_of_weak_spec_of_not_injects_into_omega hx

end pSet

namespace bSet

variable {𝔹 : Type u} [CompleteBooleanAlgebra 𝔹]

local infix:65 " ⟹ " => lattice.imp

/-- A Boolean-valued relation on `x` is a subset of `x × x`. -/
@[reducible] def is_rel (r x : bSet 𝔹) : 𝔹 :=
  r ⊆ᴮ prod x x

lemma B_congr_image_left (y f : bSet 𝔹) :
    B_congr (fun x : bSet 𝔹 => image x y f) := by
  intro x x'
  apply mem_ext
  · apply le_iInf
    intro z
    apply lattice.bv_imp_intro
    let Γ : 𝔹 := x =ᴮ x' ⊓ z ∈ᴮ image x y f
    change Γ ≤ z ∈ᴮ image x' y f
    have hzInfo := (mem_image_iff.mp (inf_le_right : Γ ≤ z ∈ᴮ image x y f))
    rw [mem_image_iff]
    refine ⟨hzInfo.1, ?_⟩
    apply (le_inf le_rfl hzInfo.2).trans
    apply lattice.bv_cases_right
    intro a
    apply lattice.bv_use a
    apply le_inf
    · exact subst_congr_mem_right' (inf_le_left.trans inf_le_left)
        (inf_le_right.trans inf_le_left)
    · exact inf_le_right.trans inf_le_right
  · apply le_iInf
    intro z
    apply lattice.bv_imp_intro
    let Γ : 𝔹 := x =ᴮ x' ⊓ z ∈ᴮ image x' y f
    change Γ ≤ z ∈ᴮ image x y f
    have hzInfo := (mem_image_iff.mp (inf_le_right : Γ ≤ z ∈ᴮ image x' y f))
    rw [mem_image_iff]
    refine ⟨hzInfo.1, ?_⟩
    apply (le_inf le_rfl hzInfo.2).trans
    apply lattice.bv_cases_right
    intro a
    apply lattice.bv_use a
    apply le_inf
    · exact subst_congr_mem_right' (bv_symm (inf_le_left.trans inf_le_left))
        (inf_le_right.trans inf_le_left)
    · exact inf_le_right.trans inf_le_right

lemma B_congr_image_right (x y : bSet 𝔹) :
    B_congr (fun f : bSet 𝔹 => image x y f) := by
  intro f f'
  apply mem_ext
  · apply le_iInf
    intro z
    apply lattice.bv_imp_intro
    let Γ : 𝔹 := f =ᴮ f' ⊓ z ∈ᴮ image x y f
    change Γ ≤ z ∈ᴮ image x y f'
    have hzInfo := (mem_image_iff.mp (inf_le_right : Γ ≤ z ∈ᴮ image x y f))
    rw [mem_image_iff]
    refine ⟨hzInfo.1, ?_⟩
    apply (le_inf le_rfl hzInfo.2).trans
    apply lattice.bv_cases_right
    intro a
    apply lattice.bv_use a
    apply le_inf
    · exact inf_le_right.trans inf_le_left
    · exact subst_congr_mem_right' (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_right)
  · apply le_iInf
    intro z
    apply lattice.bv_imp_intro
    let Γ : 𝔹 := f =ᴮ f' ⊓ z ∈ᴮ image x y f'
    change Γ ≤ z ∈ᴮ image x y f
    have hzInfo := (mem_image_iff.mp (inf_le_right : Γ ≤ z ∈ᴮ image x y f'))
    rw [mem_image_iff]
    refine ⟨hzInfo.1, ?_⟩
    apply (le_inf le_rfl hzInfo.2).trans
    apply lattice.bv_cases_right
    intro a
    apply lattice.bv_use a
    apply le_inf
    · exact inf_le_right.trans inf_le_left
    · exact subst_congr_mem_right' (bv_symm (inf_le_left.trans inf_le_left))
        (inf_le_right.trans inf_le_right)

lemma B_ext_is_injective_function_left {y f : bSet 𝔹} :
    B_ext (fun x : bSet 𝔹 => is_injective_function x y f) := by
  unfold is_injective_function
  exact B_ext_inf (B_ext_is_function_left (y := y) (f := f)) (B_ext_const (is_inj f))

lemma B_ext_is_function_codomain {x f : bSet 𝔹} :
    B_ext (fun y : bSet 𝔹 => is_function x y f) := by
  unfold is_function
  apply B_ext_inf
  · unfold is_func'
    apply B_ext_inf
    · exact B_ext_const (is_func f)
    · unfold is_total
      apply B_ext_iInf
      intro w₁
      apply B_ext_imp
      · exact B_ext_const (w₁ ∈ᴮ x)
      · apply B_ext_iSup
        intro w₂
        apply B_ext_inf
        · exact B_ext_mem_right w₂
        · exact B_ext_const (pair w₁ w₂ ∈ᴮ f)
  · exact B_ext_prod_right (B_ext_subset_right f) x

lemma B_ext_is_injective_function_codomain {x f : bSet 𝔹} :
    B_ext (fun y : bSet 𝔹 => is_injective_function x y f) := by
  unfold is_injective_function
  exact B_ext_inf (B_ext_is_function_codomain (x := x) (f := f)) (B_ext_const (is_inj f))

lemma is_injective_function_codomain_congr {x y z f : bSet 𝔹} {Γ : 𝔹}
    (hEq : Γ ≤ y =ᴮ z) (hInj : Γ ≤ is_injective_function x y f) :
    Γ ≤ is_injective_function x z f :=
  (le_inf hEq hInj).trans (B_ext_is_injective_function_codomain (x := x) (f := f) y z)

lemma is_function_codomain_congr {x y z f : bSet 𝔹} {Γ : 𝔹}
    (hEq : Γ ≤ y =ᴮ z) (hFunc : Γ ≤ is_function x y f) :
    Γ ≤ is_function x z f :=
  (le_inf hEq hFunc).trans (B_ext_is_function_codomain (x := x) (f := f) y z)

lemma B_ext_is_surj_codomain {x f : bSet 𝔹} :
    B_ext (fun y : bSet 𝔹 => is_surj x y f) := by
  unfold is_surj
  apply B_ext_iInf
  intro v
  apply B_ext_imp
  · exact B_ext_mem_right v
  · apply B_ext_iSup
    intro w
    apply B_ext_inf
    · exact B_ext_const (w ∈ᴮ x)
    · exact B_ext_const (pair w v ∈ᴮ f)

lemma is_surj_codomain_congr {x y z f : bSet 𝔹} {Γ : 𝔹}
    (hEq : Γ ≤ y =ᴮ z) (hSurj : Γ ≤ is_surj x y f) :
    Γ ≤ is_surj x z f :=
  (le_inf hEq hSurj).trans (B_ext_is_surj_codomain (x := x) (f := f) y z)

/-- Boolean-valued well-order predicate for a relation `r` on `x`. -/
def is_wo (r x : bSet 𝔹) : 𝔹 :=
  is_rel r x ⊓
    ((⨅ y : bSet 𝔹, pair y x ∈ᴮ r ⟹
      (⨅ z : bSet 𝔹, pair z x ∈ᴮ r ⟹
        ((y =ᴮ z) ⊔ pair y z ∈ᴮ r ⊔ pair z y ∈ᴮ r))) ⊓
    (⨅ u : bSet 𝔹, u ⊆ᴮ x ⟹
      ((u =ᴮ ∅)ᶜ ⟹
        ⨆ y : bSet 𝔹, pair y u ∈ᴮ r ⊓
          (⨅ z' : bSet 𝔹, pair z' u ∈ᴮ r ⟹ (pair z' y ∈ᴮ r)ᶜ))))

/-- The membership relation on a Boolean-valued ordinal candidate. -/
def mem_rel (x : bSet 𝔹) : bSet 𝔹 :=
  subset.mk (x := prod x x) (fun pr : (prod x x).type => x.func pr.1 ∈ᴮ x.func pr.2)

lemma mem_mem_rel_iff {x y z : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ pair y z ∈ᴮ mem_rel x ↔ Γ ≤ y ∈ᴮ x ∧ Γ ≤ z ∈ᴮ x ∧ Γ ≤ y ∈ᴮ z := by
  constructor
  · intro h
    have hProd : Γ ≤ pair y z ∈ᴮ prod x x :=
      mem_of_mem_subset' subset.mk_subset h
    refine ⟨(mem_prod_iff.mp hProd).1, (mem_prod_iff.mp hProd).2, ?_⟩
    unfold mem_rel at h
    rw [mem_subset.mk_iff₂] at h
    apply (le_inf le_rfl h).trans
    apply lattice.bv_cases_right
    intro pr
    let Δ : 𝔹 := Γ ⊓ ((prod x x).bval pr ⊓
      (pair y z =ᴮ (prod x x).func pr ⊓ x.func pr.1 ∈ᴮ x.func pr.2))
    change Δ ≤ y ∈ᴮ z
    have hPairEq : Δ ≤ pair y z =ᴮ pair (x.func pr.1) (x.func pr.2) := by
      dsimp [Δ, bSet.prod]
      exact inf_le_right.trans inf_le_right |>.trans inf_le_left
    have hyEq : Δ ≤ y =ᴮ x.func pr.1 := eq_of_eq_pair_left' hPairEq
    have hzEq : Δ ≤ z =ᴮ x.func pr.2 := eq_of_eq_pair_right' hPairEq
    have hMem : Δ ≤ x.func pr.1 ∈ᴮ x.func pr.2 := by
      dsimp [Δ]
      exact inf_le_right.trans inf_le_right |>.trans inf_le_right
    exact subst_congr_mem_right' (bv_symm hzEq) (subst_congr_mem_left' (bv_symm hyEq) hMem)
  · rintro ⟨hyx, hzx, hyz⟩
    unfold mem_rel
    rw [mem_subset.mk_iff₂]
    rw [mem_unfold] at hyx
    apply (le_inf le_rfl hyx).trans
    apply lattice.bv_cases_right
    intro i
    let Γi : 𝔹 := Γ ⊓ (x.bval i ⊓ y =ᴮ x.func i)
    have hzxi : Γi ≤ z ∈ᴮ x := inf_le_left.trans hzx
    rw [mem_unfold] at hzxi
    apply (le_inf le_rfl hzxi).trans
    apply lattice.bv_cases_right
    intro j
    let Γij : 𝔹 := Γi ⊓ (x.bval j ⊓ z =ᴮ x.func j)
    apply lattice.bv_use (i, j)
    apply le_inf
    · dsimp [Γij, Γi, bSet.prod]
      exact le_inf
        (inf_le_left.trans (inf_le_right.trans inf_le_left))
        (inf_le_right.trans inf_le_left)
    · apply le_inf
      · have hyEq : Γij ≤ y =ᴮ x.func i := by
          dsimp [Γij, Γi]
          exact inf_le_left.trans (inf_le_right.trans inf_le_right)
        have hzEq : Γij ≤ z =ᴮ x.func j := by
          dsimp [Γij]
          exact inf_le_right.trans inf_le_right
        exact pair_congr hyEq hzEq
      · have hyEq : Γij ≤ y =ᴮ x.func i := by
          dsimp [Γij, Γi]
          exact inf_le_left.trans (inf_le_right.trans inf_le_right)
        have hzEq : Γij ≤ z =ᴮ x.func j := by
          dsimp [Γij]
          exact inf_le_right.trans inf_le_right
        exact subst_congr_mem_right' hzEq
          (subst_congr_mem_left' hyEq ((inf_le_left.trans inf_le_left).trans hyz))

lemma B_congr_mem_rel : B_congr (mem_rel : bSet 𝔹 → bSet 𝔹) := by
  intro x y
  apply prod_ext (x := y) (y := y)
  · exact subst_congr_subset_right' (prod_congr le_rfl le_rfl) subset.mk_subset
  · exact subset.mk_subset
  · apply le_iInf
    intro v
    apply lattice.bv_imp_intro
    apply le_iInf
    intro w
    apply lattice.bv_imp_intro
    apply lattice.bv_biimp_iff.mpr
    intro Θ hΘ
    constructor
    · intro hMem
      rcases (mem_mem_rel_iff.mp hMem) with ⟨_, _, hvw⟩
      have hvY : Θ ≤ v ∈ᴮ y := hΘ.trans (inf_le_left.trans inf_le_right)
      have hwY : Θ ≤ w ∈ᴮ y := hΘ.trans inf_le_right
      exact mem_mem_rel_iff.mpr ⟨hvY, hwY, hvw⟩
    · intro hMem
      rcases (mem_mem_rel_iff.mp hMem) with ⟨hvY, hwY, hvw⟩
      have hxy : Θ ≤ x =ᴮ y := hΘ.trans (inf_le_left.trans inf_le_left)
      have hvX : Θ ≤ v ∈ᴮ x := subst_congr_mem_right' (bv_symm hxy) hvY
      have hwX : Θ ≤ w ∈ᴮ x := subst_congr_mem_right' (bv_symm hxy) hwY
      exact mem_mem_rel_iff.mpr ⟨hvX, hwX, hvw⟩

/-- Product map induced by two Boolean-valued functions. -/
def prod.map (x y v w : bSet 𝔹) (f g : bSet 𝔹) : bSet 𝔹 :=
  subset.mk (x := prod (prod x v) (prod y w)) (fun pr : (prod (prod x v) (prod y w)).type =>
    pair (x.func pr.1.1) (y.func pr.2.1) ∈ᴮ f ⊓
      pair (v.func pr.1.2) (w.func pr.2.2) ∈ᴮ g)

/-- Product map induced by one Boolean-valued function on both coordinates. -/
def prod.map_self (x y f : bSet 𝔹) : bSet 𝔹 :=
  prod.map x y x y f f

lemma B_ext_eq_pair_left (z b : bSet 𝔹) :
    B_ext (fun a : bSet 𝔹 => z =ᴮ pair a b) := by
  intro a a'
  have hPair : a =ᴮ a' ⊓ z =ᴮ pair a b ≤ pair a b =ᴮ pair a' b :=
    pair_congr inf_le_left bv_refl
  exact (le_inf hPair inf_le_right).trans (B_ext_eq_right z (pair a b) (pair a' b))

lemma B_ext_eq_pair_right (z a : bSet 𝔹) :
    B_ext (fun b : bSet 𝔹 => z =ᴮ pair a b) := by
  intro b b'
  have hPair : b =ᴮ b' ⊓ z =ᴮ pair a b ≤ pair a b =ᴮ pair a b' :=
    pair_congr bv_refl inf_le_left
  exact (le_inf hPair inf_le_right).trans (B_ext_eq_right z (pair a b) (pair a b'))

lemma mem_prod_exists_pair {x y z : bSet 𝔹} {Γ : 𝔹}
    (h : Γ ≤ z ∈ᴮ prod x y) :
    ∃ a b : bSet 𝔹,
      Γ ≤ a ∈ᴮ x ∧ Γ ≤ b ∈ᴮ y ∧ Γ ≤ z =ᴮ pair a b := by
  have hSup : Γ ≤
      ⨆ a : bSet 𝔹, a ∈ᴮ x ⊓
        ⨆ b : bSet 𝔹, b ∈ᴮ y ⊓ z =ᴮ pair a b := by
    rw [mem_unfold] at h
    apply (le_inf le_rfl h).trans
    apply lattice.bv_cases_right
    intro ij
    let Δ : 𝔹 := Γ ⊓ ((prod x y).bval ij ⊓ z =ᴮ (prod x y).func ij)
    change Δ ≤
      ⨆ a : bSet 𝔹, a ∈ᴮ x ⊓
        ⨆ b : bSet 𝔹, b ∈ᴮ y ⊓ z =ᴮ pair a b
    apply lattice.bv_use (x.func ij.1)
    apply le_inf
    · apply mem.mk''
      dsimp [Δ, prod]
      exact inf_le_right.trans inf_le_left |>.trans inf_le_left
    · apply lattice.bv_use (y.func ij.2)
      apply le_inf
      · apply mem.mk''
        dsimp [Δ, prod]
        exact inf_le_right.trans inf_le_left |>.trans inf_le_right
      · dsimp [Δ, prod]
        exact inf_le_right.trans inf_le_right
  have hB₁ : B_ext (fun a : bSet 𝔹 =>
      a ∈ᴮ x ⊓ ⨆ b : bSet 𝔹, b ∈ᴮ y ⊓ z =ᴮ pair a b) := by
    apply B_ext_inf
    · exact B_ext_mem_left x
    · apply B_ext_iSup
      intro b
      apply B_ext_inf
      · exact B_ext_const (b ∈ᴮ y)
      · exact B_ext_eq_pair_left z b
  rcases exists_convert hSup hB₁ with ⟨a, ha⟩
  have hSupB : Γ ≤ ⨆ b : bSet 𝔹, b ∈ᴮ y ⊓ z =ᴮ pair a b :=
    ha.trans inf_le_right
  have hB₂ : B_ext (fun b : bSet 𝔹 => b ∈ᴮ y ⊓ z =ᴮ pair a b) := by
    apply B_ext_inf
    · exact B_ext_mem_left y
    · exact B_ext_eq_pair_right z a
  rcases exists_convert hSupB hB₂ with ⟨b, hb⟩
  exact ⟨a, b, ha.trans inf_le_left, hb.trans inf_le_left, hb.trans inf_le_right⟩

lemma prod_map_self_subset_of_eq {x x' y f : bSet 𝔹} {Γ : 𝔹}
    (hEq : Γ ≤ x =ᴮ x') :
    Γ ≤ prod.map_self x y f ⊆ᴮ prod.map_self x' y f := by
  apply subset_intro
  intro pr
  let Δ : 𝔹 := Γ ⊓ (prod.map_self x y f).bval pr
  change Δ ≤ (prod.map_self x y f).func pr ∈ᴮ prod.map_self x' y f
  have hΔEq : Δ ≤ x =ᴮ x' := inf_le_left.trans hEq
  have ha₁MemX : Δ ≤ x.func pr.1.1 ∈ᴮ x := by
    apply mem.mk''
    dsimp [Δ, prod.map_self, prod.map, prod]
    exact inf_le_right.trans inf_le_right |>.trans inf_le_left |>.trans inf_le_left
  have ha₂MemX : Δ ≤ x.func pr.1.2 ∈ᴮ x := by
    apply mem.mk''
    dsimp [Δ, prod.map_self, prod.map, prod]
    exact inf_le_right.trans inf_le_right |>.trans inf_le_left |>.trans inf_le_right
  have ha₁MemX' : Δ ≤ x.func pr.1.1 ∈ᴮ x' :=
    subst_congr_mem_right' hΔEq ha₁MemX
  have ha₂MemX' : Δ ≤ x.func pr.1.2 ∈ᴮ x' :=
    subst_congr_mem_right' hΔEq ha₂MemX
  rw [mem_unfold] at ha₁MemX'
  apply (le_inf le_rfl ha₁MemX').trans
  apply lattice.bv_cases_right
  intro a₁'
  let Δ₁ : 𝔹 := Δ ⊓ (x'.bval a₁' ⊓ x.func pr.1.1 =ᴮ x'.func a₁')
  have ha₂MemX'_Δ₁ : Δ₁ ≤ x.func pr.1.2 ∈ᴮ x' := inf_le_left.trans ha₂MemX'
  rw [mem_unfold] at ha₂MemX'_Δ₁
  apply (le_inf le_rfl ha₂MemX'_Δ₁).trans
  apply lattice.bv_cases_right
  intro a₂'
  let Δ₂ : 𝔹 := Δ₁ ⊓ (x'.bval a₂' ⊓ x.func pr.1.2 =ᴮ x'.func a₂')
  change Δ₂ ≤ pair (pair (x.func pr.1.1) (x.func pr.1.2))
      (pair (y.func pr.2.1) (y.func pr.2.2)) ∈ᴮ prod.map_self x' y f
  rw [prod.map_self, prod.map, mem_subset.mk_iff₂]
  apply lattice.bv_use ((a₁', a₂'), pr.2)
  apply le_inf
  · have ha₁'Val : Δ₂ ≤ x'.bval a₁' := by
      dsimp [Δ₂, Δ₁]
      exact inf_le_left.trans inf_le_right |>.trans inf_le_left
    have ha₂'Val : Δ₂ ≤ x'.bval a₂' := by
      dsimp [Δ₂]
      exact inf_le_right.trans inf_le_left
    have hb₁Val : Δ₂ ≤ y.bval pr.2.1 := by
      dsimp [Δ₂, Δ₁, Δ, prod.map_self, prod.map, prod]
      exact inf_le_left.trans inf_le_left |>.trans inf_le_right |>.trans inf_le_right |>.trans
        inf_le_right |>.trans inf_le_left
    have hb₂Val : Δ₂ ≤ y.bval pr.2.2 := by
      dsimp [Δ₂, Δ₁, Δ, prod.map_self, prod.map, prod]
      exact inf_le_left.trans inf_le_left |>.trans inf_le_right |>.trans inf_le_right |>.trans
        inf_le_right |>.trans inf_le_right
    dsimp [prod]
    exact le_inf (le_inf ha₁'Val ha₂'Val) (le_inf hb₁Val hb₂Val)
  · apply le_inf
    · have ha₁Eq : Δ₂ ≤ x.func pr.1.1 =ᴮ x'.func a₁' := by
        dsimp [Δ₂, Δ₁]
        exact inf_le_left.trans inf_le_right |>.trans inf_le_right
      have ha₂Eq : Δ₂ ≤ x.func pr.1.2 =ᴮ x'.func a₂' := by
        dsimp [Δ₂]
        exact inf_le_right.trans inf_le_right
      apply pair_congr
      · exact pair_congr ha₁Eq ha₂Eq
      · exact bv_refl
    · apply le_inf
      · have ha₁Eq : Δ₂ ≤ x.func pr.1.1 =ᴮ x'.func a₁' := by
          dsimp [Δ₂, Δ₁]
          exact inf_le_left.trans inf_le_right |>.trans inf_le_right
        have hPairMem : Δ₂ ≤ pair (x.func pr.1.1) (y.func pr.2.1) ∈ᴮ f := by
          dsimp [Δ₂, Δ₁, Δ, prod.map_self, prod.map]
          exact inf_le_left.trans inf_le_left |>.trans inf_le_right |>.trans inf_le_left |>.trans
            inf_le_left
        exact subst_congr_mem_left' (pair_congr ha₁Eq bv_refl) hPairMem
      · have ha₂Eq : Δ₂ ≤ x.func pr.1.2 =ᴮ x'.func a₂' := by
          dsimp [Δ₂]
          exact inf_le_right.trans inf_le_right
        have hPairMem : Δ₂ ≤ pair (x.func pr.1.2) (y.func pr.2.2) ∈ᴮ f := by
          dsimp [Δ₂, Δ₁, Δ, prod.map_self, prod.map]
          exact inf_le_left.trans inf_le_left |>.trans inf_le_right |>.trans inf_le_left |>.trans
            inf_le_right
        exact subst_congr_mem_left' (pair_congr ha₂Eq bv_refl) hPairMem

lemma B_congr_prod_map_self_left {y f : bSet 𝔹} :
    B_congr (fun x : bSet 𝔹 => prod.map_self x y f) := by
  intro x x'
  apply subset_ext
  · exact prod_map_self_subset_of_eq le_rfl
  · exact prod_map_self_subset_of_eq (bv_symm (le_rfl : x =ᴮ x' ≤ x =ᴮ x'))

lemma mem_prod_map_self_iff {x y f a₁ a₂ b₁ b₂ : bSet 𝔹} {Γ : 𝔹}
    (_H_func : Γ ≤ is_function x y f) :
    Γ ≤ pair (pair a₁ a₂) (pair b₁ b₂) ∈ᴮ prod.map_self x y f ↔
      Γ ≤ a₁ ∈ᴮ x ∧ Γ ≤ a₂ ∈ᴮ x ∧ Γ ≤ b₁ ∈ᴮ y ∧ Γ ≤ b₂ ∈ᴮ y ∧
        Γ ≤ pair a₁ b₁ ∈ᴮ f ∧ Γ ≤ pair a₂ b₂ ∈ᴮ f := by
  constructor
  · intro h
    rw [prod.map_self, prod.map, mem_subset.mk_iff₂] at h
    have hAll : Γ ≤
        a₁ ∈ᴮ x ⊓ (a₂ ∈ᴮ x ⊓ (b₁ ∈ᴮ y ⊓ (b₂ ∈ᴮ y ⊓
          (pair a₁ b₁ ∈ᴮ f ⊓ pair a₂ b₂ ∈ᴮ f)))) := by
      apply (le_inf le_rfl h).trans
      apply lattice.bv_cases_right
      intro pr
      let Δ : 𝔹 := Γ ⊓ ((prod (prod x x) (prod y y)).bval pr ⊓
        (pair (pair a₁ a₂) (pair b₁ b₂) =ᴮ
          (prod (prod x x) (prod y y)).func pr ⊓
            (pair (x.func pr.1.1) (y.func pr.2.1) ∈ᴮ f ⊓
              pair (x.func pr.1.2) (y.func pr.2.2) ∈ᴮ f)))
      change Δ ≤
        a₁ ∈ᴮ x ⊓ (a₂ ∈ᴮ x ⊓ (b₁ ∈ᴮ y ⊓ (b₂ ∈ᴮ y ⊓
          (pair a₁ b₁ ∈ᴮ f ⊓ pair a₂ b₂ ∈ᴮ f))))
      have hEqOuter : Δ ≤ pair (pair a₁ a₂) (pair b₁ b₂) =ᴮ
          pair (pair (x.func pr.1.1) (x.func pr.1.2))
            (pair (y.func pr.2.1) (y.func pr.2.2)) := by
        dsimp [Δ, prod]
        exact inf_le_right.trans inf_le_right |>.trans inf_le_left
      have hLeftPair : Δ ≤ pair a₁ a₂ =ᴮ pair (x.func pr.1.1) (x.func pr.1.2) :=
        eq_of_eq_pair_left' hEqOuter
      have hRightPair : Δ ≤ pair b₁ b₂ =ᴮ pair (y.func pr.2.1) (y.func pr.2.2) :=
        eq_of_eq_pair_right' hEqOuter
      have ha₁Eq : Δ ≤ a₁ =ᴮ x.func pr.1.1 := eq_of_eq_pair_left' hLeftPair
      have ha₂Eq : Δ ≤ a₂ =ᴮ x.func pr.1.2 := eq_of_eq_pair_right' hLeftPair
      have hb₁Eq : Δ ≤ b₁ =ᴮ y.func pr.2.1 := eq_of_eq_pair_left' hRightPair
      have hb₂Eq : Δ ≤ b₂ =ᴮ y.func pr.2.2 := eq_of_eq_pair_right' hRightPair
      have ha₁Mem : Δ ≤ a₁ ∈ᴮ x := by
        have hmem : Δ ≤ x.func pr.1.1 ∈ᴮ x := by
          apply mem.mk''
          dsimp [Δ, prod]
          exact inf_le_right.trans inf_le_left |>.trans inf_le_left |>.trans inf_le_left
        exact subst_congr_mem_left' (bv_symm ha₁Eq) hmem
      have ha₂Mem : Δ ≤ a₂ ∈ᴮ x := by
        have hmem : Δ ≤ x.func pr.1.2 ∈ᴮ x := by
          apply mem.mk''
          dsimp [Δ, prod]
          exact inf_le_right.trans inf_le_left |>.trans inf_le_left |>.trans inf_le_right
        exact subst_congr_mem_left' (bv_symm ha₂Eq) hmem
      have hb₁Mem : Δ ≤ b₁ ∈ᴮ y := by
        have hmem : Δ ≤ y.func pr.2.1 ∈ᴮ y := by
          apply mem.mk''
          dsimp [Δ, prod]
          exact inf_le_right.trans inf_le_left |>.trans inf_le_right |>.trans inf_le_left
        exact subst_congr_mem_left' (bv_symm hb₁Eq) hmem
      have hb₂Mem : Δ ≤ b₂ ∈ᴮ y := by
        have hmem : Δ ≤ y.func pr.2.2 ∈ᴮ y := by
          apply mem.mk''
          dsimp [Δ, prod]
          exact inf_le_right.trans inf_le_left |>.trans inf_le_right |>.trans inf_le_right
        exact subst_congr_mem_left' (bv_symm hb₂Eq) hmem
      have hf₁ : Δ ≤ pair a₁ b₁ ∈ᴮ f := by
        have hmem : Δ ≤ pair (x.func pr.1.1) (y.func pr.2.1) ∈ᴮ f := by
          dsimp [Δ]
          exact inf_le_right.trans inf_le_right |>.trans inf_le_right |>.trans inf_le_left
        exact subst_congr_mem_left' (pair_congr (bv_symm ha₁Eq) (bv_symm hb₁Eq)) hmem
      have hf₂ : Δ ≤ pair a₂ b₂ ∈ᴮ f := by
        have hmem : Δ ≤ pair (x.func pr.1.2) (y.func pr.2.2) ∈ᴮ f := by
          dsimp [Δ]
          exact inf_le_right.trans inf_le_right |>.trans inf_le_right |>.trans inf_le_right
        exact subst_congr_mem_left' (pair_congr (bv_symm ha₂Eq) (bv_symm hb₂Eq)) hmem
      exact le_inf ha₁Mem (le_inf ha₂Mem (le_inf hb₁Mem (le_inf hb₂Mem (le_inf hf₁ hf₂))))
    exact ⟨hAll.trans inf_le_left,
      hAll.trans (inf_le_right.trans inf_le_left),
      hAll.trans (inf_le_right.trans (inf_le_right.trans inf_le_left)),
      hAll.trans (inf_le_right.trans (inf_le_right.trans (inf_le_right.trans inf_le_left))),
      hAll.trans (inf_le_right.trans (inf_le_right.trans (inf_le_right.trans (inf_le_right.trans inf_le_left)))),
      hAll.trans (inf_le_right.trans (inf_le_right.trans (inf_le_right.trans (inf_le_right.trans inf_le_right))))⟩
  · rintro ⟨ha₁Mem, ha₂Mem, hb₁Mem, hb₂Mem, hf₁, hf₂⟩
    rw [prod.map_self, prod.map, mem_subset.mk_iff₂]
    rw [mem_unfold] at ha₁Mem ha₂Mem hb₁Mem hb₂Mem
    apply (le_inf le_rfl ha₁Mem).trans
    apply lattice.bv_cases_right
    intro i₁
    let Γ₁ : 𝔹 := Γ ⊓ (x.bval i₁ ⊓ a₁ =ᴮ x.func i₁)
    change Γ₁ ≤
      ⨆ i : (prod (prod x x) (prod y y)).type,
        (prod (prod x x) (prod y y)).bval i ⊓
          (pair (pair a₁ a₂) (pair b₁ b₂) =ᴮ
            (prod (prod x x) (prod y y)).func i ⊓
              (pair (x.func i.1.1) (y.func i.2.1) ∈ᴮ f ⊓
                pair (x.func i.1.2) (y.func i.2.2) ∈ᴮ f))
    apply (le_inf le_rfl (inf_le_left.trans ha₂Mem)).trans
    apply lattice.bv_cases_right
    intro i₂
    let Γ₂ : 𝔹 := Γ₁ ⊓ (x.bval i₂ ⊓ a₂ =ᴮ x.func i₂)
    change Γ₂ ≤
      ⨆ i : (prod (prod x x) (prod y y)).type,
        (prod (prod x x) (prod y y)).bval i ⊓
          (pair (pair a₁ a₂) (pair b₁ b₂) =ᴮ
            (prod (prod x x) (prod y y)).func i ⊓
              (pair (x.func i.1.1) (y.func i.2.1) ∈ᴮ f ⊓
                pair (x.func i.1.2) (y.func i.2.2) ∈ᴮ f))
    apply (le_inf le_rfl (inf_le_left.trans (inf_le_left.trans hb₁Mem))).trans
    apply lattice.bv_cases_right
    intro j₁
    let Γ₃ : 𝔹 := Γ₂ ⊓ (y.bval j₁ ⊓ b₁ =ᴮ y.func j₁)
    change Γ₃ ≤
      ⨆ i : (prod (prod x x) (prod y y)).type,
        (prod (prod x x) (prod y y)).bval i ⊓
          (pair (pair a₁ a₂) (pair b₁ b₂) =ᴮ
            (prod (prod x x) (prod y y)).func i ⊓
              (pair (x.func i.1.1) (y.func i.2.1) ∈ᴮ f ⊓
                pair (x.func i.1.2) (y.func i.2.2) ∈ᴮ f))
    apply (le_inf le_rfl (inf_le_left.trans (inf_le_left.trans (inf_le_left.trans hb₂Mem)))).trans
    apply lattice.bv_cases_right
    intro j₂
    let Γ₄ : 𝔹 := Γ₃ ⊓ (y.bval j₂ ⊓ b₂ =ᴮ y.func j₂)
    change Γ₄ ≤
      ⨆ i : (prod (prod x x) (prod y y)).type,
        (prod (prod x x) (prod y y)).bval i ⊓
          (pair (pair a₁ a₂) (pair b₁ b₂) =ᴮ
            (prod (prod x x) (prod y y)).func i ⊓
              (pair (x.func i.1.1) (y.func i.2.1) ∈ᴮ f ⊓
                pair (x.func i.1.2) (y.func i.2.2) ∈ᴮ f))
    apply lattice.bv_use ((i₁, i₂), (j₁, j₂))
    apply le_inf
    · dsimp [Γ₄, Γ₃, Γ₂, Γ₁, prod]
      exact le_inf
        (le_inf
          (inf_le_left.trans (inf_le_left.trans (inf_le_left.trans (inf_le_right.trans inf_le_left))))
          (inf_le_left.trans (inf_le_left.trans (inf_le_right.trans inf_le_left))))
        (le_inf
          (inf_le_left.trans (inf_le_right.trans inf_le_left))
          (inf_le_right.trans inf_le_left))
    · apply le_inf
      · dsimp [Γ₄, Γ₃, Γ₂, Γ₁, prod]
        apply pair_congr
        · exact pair_congr
            (inf_le_left.trans (inf_le_left.trans (inf_le_left.trans (inf_le_right.trans inf_le_right))))
            (inf_le_left.trans (inf_le_left.trans (inf_le_right.trans inf_le_right)))
        · exact pair_congr
            (inf_le_left.trans (inf_le_right.trans inf_le_right))
            (inf_le_right.trans inf_le_right)
      · apply le_inf
        · have hEq : Γ₄ ≤ pair a₁ b₁ =ᴮ pair (x.func i₁) (y.func j₁) := by
            dsimp [Γ₄, Γ₃, Γ₂, Γ₁]
            exact pair_congr
              (inf_le_left.trans (inf_le_left.trans (inf_le_left.trans (inf_le_right.trans inf_le_right))))
              (inf_le_left.trans (inf_le_right.trans inf_le_right))
          exact subst_congr_mem_left' hEq (inf_le_left.trans (inf_le_left.trans (inf_le_left.trans (inf_le_left.trans hf₁))))
        · have hEq : Γ₄ ≤ pair a₂ b₂ =ᴮ pair (x.func i₂) (y.func j₂) := by
            dsimp [Γ₄, Γ₃, Γ₂, Γ₁]
            exact pair_congr
              (inf_le_left.trans (inf_le_left.trans (inf_le_right.trans inf_le_right)))
              (inf_le_right.trans inf_le_right)
          exact subst_congr_mem_left' hEq (inf_le_left.trans (inf_le_left.trans (inf_le_left.trans (inf_le_left.trans hf₂))))

/-- The epsilon relation on `η`, transported along an internal map `f : η → x`. -/
def induced_epsilon_rel (η x f : bSet 𝔹) : bSet 𝔹 :=
  image (mem_rel η) (prod x x) (prod.map_self η x f)

lemma eq_pair_of_mem_induced_epsilon_rel {η x f pr : bSet 𝔹} {Γ : 𝔹}
    (hMem : Γ ≤ pr ∈ᴮ induced_epsilon_rel η x f) :
    ∃ a b : bSet 𝔹,
      Γ ≤ a ∈ᴮ x ∧ Γ ≤ b ∈ᴮ x ∧ Γ ≤ pr =ᴮ pair a b ∧
        Γ ≤ pair a b ∈ᴮ induced_epsilon_rel η x f := by
  have hProd : Γ ≤ pr ∈ᴮ prod x x :=
    mem_of_mem_subset' image_subset hMem
  rcases mem_prod_exists_pair hProd with ⟨a, b, ha, hb, hEq⟩
  have hPairMem : Γ ≤ pair a b ∈ᴮ induced_epsilon_rel η x f :=
    subst_congr_mem_left' hEq hMem
  exact ⟨a, b, ha, hb, hEq, hPairMem⟩

lemma mem_induced_epsilon_rel_iff {η x f a b : bSet 𝔹} {Γ : 𝔹}
    (hFunc : Γ ≤ is_function η x f) :
    Γ ≤ pair a b ∈ᴮ induced_epsilon_rel η x f ↔
      Γ ≤ a ∈ᴮ x ∧ Γ ≤ b ∈ᴮ x ∧
        Γ ≤ ⨆ a' : bSet 𝔹, a' ∈ᴮ η ⊓
          ⨆ b' : bSet 𝔹, b' ∈ᴮ η ⊓
            (pair a' a ∈ᴮ f ⊓ pair b' b ∈ᴮ f ⊓ a' ∈ᴮ b') := by
  constructor
  · intro h
    have hImg := (mem_image_iff (x := mem_rel η) (y := prod x x)
      (b := pair a b) (f := prod.map_self η x f) (Γ := Γ)).mp h
    have ha : Γ ≤ a ∈ᴮ x := (mem_prod_iff.mp hImg.1).1
    have hb : Γ ≤ b ∈ᴮ x := (mem_prod_iff.mp hImg.1).2
    have hThird : Γ ≤ ⨆ a' : bSet 𝔹, a' ∈ᴮ η ⊓
        ⨆ b' : bSet 𝔹, b' ∈ᴮ η ⊓
          (pair a' a ∈ᴮ f ⊓ pair b' b ∈ᴮ f ⊓ a' ∈ᴮ b') := by
      apply (le_inf le_rfl hImg.2).trans
      apply lattice.bv_cases_right
      intro z
      let Δ : 𝔹 := Γ ⊓ (z ∈ᴮ mem_rel η ⊓ pair z (pair a b) ∈ᴮ prod.map_self η x f)
      change Δ ≤ ⨆ a' : bSet 𝔹, a' ∈ᴮ η ⊓
        ⨆ b' : bSet 𝔹, b' ∈ᴮ η ⊓
          (pair a' a ∈ᴮ f ⊓ pair b' b ∈ᴮ f ⊓ a' ∈ᴮ b')
      have hzRel : Δ ≤ z ∈ᴮ mem_rel η := by
        dsimp [Δ]
        exact inf_le_right.trans inf_le_left
      have hzProd : Δ ≤ z ∈ᴮ prod η η :=
        mem_of_mem_subset' subset.mk_subset hzRel
      rcases mem_prod_exists_pair hzProd with ⟨v, w, hv, hw, hEq⟩
      apply lattice.bv_use v
      apply le_inf
      · exact hv
      · apply lattice.bv_use w
        apply le_inf
        · exact hw
        · have hMap : Δ ≤ pair (pair v w) (pair a b) ∈ᴮ prod.map_self η x f := by
            have hPairMem : Δ ≤ pair z (pair a b) ∈ᴮ prod.map_self η x f := by
              dsimp [Δ]
              exact inf_le_right.trans inf_le_right
            exact subst_congr_mem_left' (subst_congr_pair_left hEq) hPairMem
          have hFuncΔ : Δ ≤ is_function η x f := inf_le_left.trans hFunc
          have hPieces := (mem_prod_map_self_iff hFuncΔ).mp hMap
          have hRelVW : Δ ≤ pair v w ∈ᴮ mem_rel η := by
            exact subst_congr_mem_left' hEq hzRel
          have hvw : Δ ≤ v ∈ᴮ w := (mem_mem_rel_iff.mp hRelVW).2.2
          exact le_inf (le_inf hPieces.2.2.2.2.1 hPieces.2.2.2.2.2) hvw
    exact ⟨ha, hb, hThird⟩
  · rintro ⟨ha, hb, hThird⟩
    change Γ ≤ pair a b ∈ᴮ image (mem_rel η) (prod x x) (prod.map_self η x f)
    rw [mem_image_iff]
    constructor
    · exact mem_prod ha hb
    · apply (le_inf le_rfl hThird).trans
      apply lattice.bv_cases_right
      intro a'
      let Δ : 𝔹 := Γ ⊓ (a' ∈ᴮ η ⊓
        ⨆ b' : bSet 𝔹, b' ∈ᴮ η ⊓
          (pair a' a ∈ᴮ f ⊓ pair b' b ∈ᴮ f ⊓ a' ∈ᴮ b'))
      change Δ ≤ ⨆ z : bSet 𝔹, z ∈ᴮ mem_rel η ⊓
        pair z (pair a b) ∈ᴮ prod.map_self η x f
      have ha' : Δ ≤ a' ∈ᴮ η := by
        dsimp [Δ]
        exact inf_le_right.trans inf_le_left
      have hCases : Δ ≤ ⨆ b' : bSet 𝔹, b' ∈ᴮ η ⊓
          (pair a' a ∈ᴮ f ⊓ pair b' b ∈ᴮ f ⊓ a' ∈ᴮ b') := by
        dsimp [Δ]
        exact inf_le_right.trans inf_le_right
      apply (le_inf le_rfl hCases).trans
      apply lattice.bv_cases_right
      intro b'
      let Θ : 𝔹 := Δ ⊓ (b' ∈ᴮ η ⊓
        (pair a' a ∈ᴮ f ⊓ pair b' b ∈ᴮ f ⊓ a' ∈ᴮ b'))
      change Θ ≤ ⨆ z : bSet 𝔹, z ∈ᴮ mem_rel η ⊓
        pair z (pair a b) ∈ᴮ prod.map_self η x f
      have hb' : Θ ≤ b' ∈ᴮ η := by
        dsimp [Θ]
        exact inf_le_right.trans inf_le_left
      have hf₁ : Θ ≤ pair a' a ∈ᴮ f := by
        dsimp [Θ]
        exact inf_le_right.trans inf_le_right |>.trans (inf_le_left.trans inf_le_left)
      have hf₂ : Θ ≤ pair b' b ∈ᴮ f := by
        dsimp [Θ]
        exact inf_le_right.trans inf_le_right |>.trans (inf_le_left.trans inf_le_right)
      have ha'b' : Θ ≤ a' ∈ᴮ b' := by
        dsimp [Θ]
        exact inf_le_right.trans inf_le_right |>.trans inf_le_right
      apply lattice.bv_use (pair a' b')
      apply le_inf
      · exact mem_mem_rel_iff.mpr ⟨inf_le_left.trans ha', hb', ha'b'⟩
      · have hFuncΘ : Θ ≤ is_function η x f := by
          dsimp [Θ, Δ]
          exact inf_le_left.trans (inf_le_left.trans hFunc)
        exact (mem_prod_map_self_iff hFuncΘ).mpr
          ⟨inf_le_left.trans ha', hb', inf_le_left.trans (inf_le_left.trans ha),
            inf_le_left.trans (inf_le_left.trans hb),
            hf₁, hf₂⟩

lemma mem_of_mem_induced_epsilon_rel {η x f a' b' a b : bSet 𝔹} {Γ : 𝔹}
    (hInjFunc : Γ ≤ is_injective_function η x f)
    (hMem₁ : Γ ≤ pair a' a ∈ᴮ f) (hMem₂ : Γ ≤ pair b' b ∈ᴮ f)
    (hMem : Γ ≤ pair a b ∈ᴮ induced_epsilon_rel η x f) :
    Γ ≤ a' ∈ᴮ b' := by
  have hFunc : Γ ≤ is_function η x f :=
    is_function_of_is_injective_function hInjFunc
  have hRel := (mem_induced_epsilon_rel_iff hFunc).mp hMem
  apply (le_inf le_rfl hRel.2.2).trans
  apply lattice.bv_cases_right
  intro a''
  let Δ : 𝔹 := Γ ⊓ (a'' ∈ᴮ η ⊓
    ⨆ b'' : bSet 𝔹, b'' ∈ᴮ η ⊓
      (pair a'' a ∈ᴮ f ⊓ pair b'' b ∈ᴮ f ⊓ a'' ∈ᴮ b''))
  change Δ ≤ a' ∈ᴮ b'
  have hCases : Δ ≤ ⨆ b'' : bSet 𝔹, b'' ∈ᴮ η ⊓
      (pair a'' a ∈ᴮ f ⊓ pair b'' b ∈ᴮ f ⊓ a'' ∈ᴮ b'') := by
    dsimp [Δ]
    exact inf_le_right.trans inf_le_right
  apply (le_inf le_rfl hCases).trans
  apply lattice.bv_cases_right
  intro b''
  let Θ : 𝔹 := Δ ⊓ (b'' ∈ᴮ η ⊓
    (pair a'' a ∈ᴮ f ⊓ pair b'' b ∈ᴮ f ⊓ a'' ∈ᴮ b''))
  change Θ ≤ a' ∈ᴮ b'
  have hΘΓ : Θ ≤ Γ := by
    dsimp [Θ, Δ]
    exact inf_le_left.trans inf_le_left
  have hPairA'' : Θ ≤ pair a'' a ∈ᴮ f := by
    dsimp [Θ]
    exact inf_le_right.trans inf_le_right |>.trans (inf_le_left.trans inf_le_left)
  have hPairB'' : Θ ≤ pair b'' b ∈ᴮ f := by
    dsimp [Θ]
    exact inf_le_right.trans inf_le_right |>.trans (inf_le_left.trans inf_le_right)
  have hA''MemB'' : Θ ≤ a'' ∈ᴮ b'' := by
    dsimp [Θ]
    exact inf_le_right.trans inf_le_right |>.trans inf_le_right
  have hInj : Θ ≤ is_inj f :=
    hΘΓ.trans (is_inj_of_is_injective_function hInjFunc)
  have hAeq : Θ ≤ a' =ᴮ a'' := by
    have hImp : Θ ≤ lattice.imp
        (pair a' a ∈ᴮ f ⊓ pair a'' a ∈ᴮ f ⊓ a =ᴮ a) (a' =ᴮ a'') :=
      ((((hInj.trans (iInf_le _ a')).trans (iInf_le _ a'')).trans (iInf_le _ a)).trans
        (iInf_le _ a))
    exact lattice.bv_context_apply hImp
      (le_inf (le_inf (hΘΓ.trans hMem₁) hPairA'') bv_refl)
  have hBeq : Θ ≤ b' =ᴮ b'' := by
    have hImp : Θ ≤ lattice.imp
        (pair b' b ∈ᴮ f ⊓ pair b'' b ∈ᴮ f ⊓ b =ᴮ b) (b' =ᴮ b'') :=
      ((((hInj.trans (iInf_le _ b')).trans (iInf_le _ b'')).trans (iInf_le _ b)).trans
        (iInf_le _ b))
    exact lattice.bv_context_apply hImp
      (le_inf (le_inf (hΘΓ.trans hMem₂) hPairB'') bv_refl)
  have hLeft : Θ ≤ a' ∈ᴮ b'' :=
    subst_congr_mem_left' (bv_symm hAeq) hA''MemB''
  exact subst_congr_mem_right' (bv_symm hBeq) hLeft

lemma induced_epsilon_rel_sub_image_left {η x f a b : bSet 𝔹} {Γ : 𝔹}
    (hFunc : Γ ≤ is_function η x f)
    (hMem : Γ ≤ pair a b ∈ᴮ induced_epsilon_rel η x f) :
    Γ ≤ a ∈ᴮ image η x f := by
  rw [mem_image_iff]
  have hRel := (mem_induced_epsilon_rel_iff hFunc).mp hMem
  refine ⟨hRel.1, ?_⟩
  apply (le_inf le_rfl hRel.2.2).trans
  apply lattice.bv_cases_right
  intro a'
  let Δ : 𝔹 := Γ ⊓ (a' ∈ᴮ η ⊓
    ⨆ b' : bSet 𝔹, b' ∈ᴮ η ⊓
      (pair a' a ∈ᴮ f ⊓ pair b' b ∈ᴮ f ⊓ a' ∈ᴮ b'))
  change Δ ≤ ⨆ z : bSet 𝔹, z ∈ᴮ η ⊓ pair z a ∈ᴮ f
  have ha' : Δ ≤ a' ∈ᴮ η := by
    dsimp [Δ]
    exact inf_le_right.trans inf_le_left
  have hCases : Δ ≤ ⨆ b' : bSet 𝔹, b' ∈ᴮ η ⊓
      (pair a' a ∈ᴮ f ⊓ pair b' b ∈ᴮ f ⊓ a' ∈ᴮ b') := by
    dsimp [Δ]
    exact inf_le_right.trans inf_le_right
  apply (le_inf le_rfl hCases).trans
  apply lattice.bv_cases_right
  intro b'
  let Θ : 𝔹 := Δ ⊓ (b' ∈ᴮ η ⊓
    (pair a' a ∈ᴮ f ⊓ pair b' b ∈ᴮ f ⊓ a' ∈ᴮ b'))
  change Θ ≤ ⨆ z : bSet 𝔹, z ∈ᴮ η ⊓ pair z a ∈ᴮ f
  apply lattice.bv_use a'
  apply le_inf
  · exact inf_le_left.trans ha'
  · dsimp [Θ]
    exact inf_le_right.trans inf_le_right |>.trans (inf_le_left.trans inf_le_left)

lemma induced_epsilon_rel_sub_image_right {η x f a b : bSet 𝔹} {Γ : 𝔹}
    (hFunc : Γ ≤ is_function η x f)
    (hMem : Γ ≤ pair a b ∈ᴮ induced_epsilon_rel η x f) :
    Γ ≤ b ∈ᴮ image η x f := by
  rw [mem_image_iff]
  have hRel := (mem_induced_epsilon_rel_iff hFunc).mp hMem
  refine ⟨hRel.2.1, ?_⟩
  apply (le_inf le_rfl hRel.2.2).trans
  apply lattice.bv_cases_right
  intro a'
  let Δ : 𝔹 := Γ ⊓ (a' ∈ᴮ η ⊓
    ⨆ b' : bSet 𝔹, b' ∈ᴮ η ⊓
      (pair a' a ∈ᴮ f ⊓ pair b' b ∈ᴮ f ⊓ a' ∈ᴮ b'))
  change Δ ≤ ⨆ z : bSet 𝔹, z ∈ᴮ η ⊓ pair z b ∈ᴮ f
  have hCases : Δ ≤ ⨆ b' : bSet 𝔹, b' ∈ᴮ η ⊓
      (pair a' a ∈ᴮ f ⊓ pair b' b ∈ᴮ f ⊓ a' ∈ᴮ b') := by
    dsimp [Δ]
    exact inf_le_right.trans inf_le_right
  apply (le_inf le_rfl hCases).trans
  apply lattice.bv_cases_right
  intro b'
  let Θ : 𝔹 := Δ ⊓ (b' ∈ᴮ η ⊓
    (pair a' a ∈ᴮ f ⊓ pair b' b ∈ᴮ f ⊓ a' ∈ᴮ b'))
  change Θ ≤ ⨆ z : bSet 𝔹, z ∈ᴮ η ⊓ pair z b ∈ᴮ f
  apply lattice.bv_use b'
  apply le_inf
  · dsimp [Θ]
    exact inf_le_right.trans inf_le_left
  · dsimp [Θ]
    exact inf_le_right.trans inf_le_right |>.trans (inf_le_left.trans inf_le_right)

lemma induced_rel_empty_of_eq_zero {η f : bSet 𝔹} {Γ : 𝔹}
    (hFunc : Γ ≤ is_function η omega f) :
    Γ ≤ η =ᴮ (0 : bSet 𝔹) → Γ ≤ induced_epsilon_rel η omega f =ᴮ ∅ := by
  intro hEqZero
  apply subset_ext
  · apply subset_intro
    intro i
    let Δ : 𝔹 := Γ ⊓ (induced_epsilon_rel η omega f).bval i
    change Δ ≤ (induced_epsilon_rel η omega f).func i ∈ᴮ (∅ : bSet 𝔹)
    rw [mem_empty]
    have hMemInd : Δ ≤ (induced_epsilon_rel η omega f).func i ∈ᴮ
        induced_epsilon_rel η omega f := by
      apply mem.mk''
      dsimp [Δ]
      exact inf_le_right
    rcases eq_pair_of_mem_induced_epsilon_rel hMemInd with
      ⟨a, _b, _ha, _hb, _hEq, hPairMem⟩
    have hImage : Δ ≤ a ∈ᴮ image η omega f :=
      induced_epsilon_rel_sub_image_left (inf_le_left.trans hFunc) hPairMem
    have hExists : Δ ≤ ⨆ z : bSet 𝔹, z ∈ᴮ η ⊓ pair z a ∈ᴮ f :=
      (mem_image_iff.mp hImage).2
    apply (le_inf le_rfl hExists).trans
    apply lattice.bv_cases_right
    intro z
    let Θ : 𝔹 := Δ ⊓ (z ∈ᴮ η ⊓ pair z a ∈ᴮ f)
    change Θ ≤ ⊥
    have hzη : Θ ≤ z ∈ᴮ η := by
      dsimp [Θ]
      exact inf_le_right.trans inf_le_left
    have hηEmpty : Θ ≤ η =ᴮ (∅ : bSet 𝔹) :=
      bv_trans ((inf_le_left.trans inf_le_left).trans hEqZero) ofNat_zero_eq_empty
    have hNoMem : Θ ≤ (z ∈ᴮ η)ᶜ :=
      (empty_iff_forall_not_mem.mp hηEmpty).trans (iInf_le _ z)
    exact (le_inf hzη hNoMem).trans (by simp)
  · exact empty_subset

lemma nonempty_of_induced_rel_nonempty {η f : bSet 𝔹} {Γ : 𝔹}
    (hFunc : Γ ≤ is_function η omega f) :
    Γ ≤ (induced_epsilon_rel η omega f =ᴮ ∅)ᶜ → Γ ≤ (η =ᴮ ∅)ᶜ := by
  intro hNonempty
  rw [le_compl_iff_disjoint_right, disjoint_iff]
  apply le_antisymm ?_ bot_le
  let Δ : 𝔹 := Γ ⊓ η =ᴮ (∅ : bSet 𝔹)
  change Δ ≤ ⊥
  have hFuncΔ : Δ ≤ is_function η omega f := inf_le_left.trans hFunc
  have hEqZero : Δ ≤ η =ᴮ (0 : bSet 𝔹) :=
    bv_trans inf_le_right (bv_symm ofNat_zero_eq_empty)
  have hIndEmpty : Δ ≤ induced_epsilon_rel η omega f =ᴮ ∅ :=
    induced_rel_empty_of_eq_zero hFuncΔ hEqZero
  have hNotIndEmpty : Δ ≤ (induced_epsilon_rel η omega f =ᴮ ∅)ᶜ :=
    inf_le_left.trans hNonempty
  exact (le_inf hIndEmpty hNotIndEmpty).trans (by simp)

lemma not_zero_of_induced_rel_nonempty {η f : bSet 𝔹} {Γ : 𝔹}
    (hFunc : Γ ≤ is_function η omega f) :
    Γ ≤ (induced_epsilon_rel η omega f =ᴮ ∅)ᶜ → Γ ≤ (η =ᴮ (0 : bSet 𝔹))ᶜ := by
  intro hNonempty
  rw [le_compl_iff_disjoint_right, disjoint_iff]
  apply le_antisymm ?_ bot_le
  let Δ : 𝔹 := Γ ⊓ η =ᴮ (0 : bSet 𝔹)
  change Δ ≤ ⊥
  have hFuncΔ : Δ ≤ is_function η omega f := inf_le_left.trans hFunc
  have hIndEmpty : Δ ≤ induced_epsilon_rel η omega f =ᴮ ∅ :=
    induced_rel_empty_of_eq_zero hFuncΔ inf_le_right
  have hNotIndEmpty : Δ ≤ (induced_epsilon_rel η omega f =ᴮ ∅)ᶜ :=
    inf_le_left.trans hNonempty
  exact (le_inf hIndEmpty hNotIndEmpty).trans (by simp)

lemma not_one_of_induced_rel_nonempty {η f : bSet 𝔹} {Γ : 𝔹}
    (hFunc : Γ ≤ is_function η omega f) :
    Γ ≤ (induced_epsilon_rel η omega f =ᴮ ∅)ᶜ → Γ ≤ (η =ᴮ (1 : bSet 𝔹))ᶜ := by
  intro hNonempty
  rw [le_compl_iff_disjoint_right, disjoint_iff]
  apply le_antisymm ?_ bot_le
  let Δ : 𝔹 := Γ ⊓ η =ᴮ (1 : bSet 𝔹)
  change Δ ≤ ⊥
  have hExists : Δ ≤ ⨆ pr : bSet 𝔹, pr ∈ᴮ induced_epsilon_rel η omega f :=
    nonempty_iff_exists_mem.mp (inf_le_left.trans hNonempty)
  apply (le_inf le_rfl hExists).trans
  apply lattice.bv_cases_right
  intro pr
  let Θ : 𝔹 := Δ ⊓ pr ∈ᴮ induced_epsilon_rel η omega f
  change Θ ≤ ⊥
  have hPr : Θ ≤ pr ∈ᴮ induced_epsilon_rel η omega f := by
    dsimp [Θ]
    exact inf_le_right
  rcases eq_pair_of_mem_induced_epsilon_rel hPr with
    ⟨a, b, _ha, _hb, _hEq, hPairMem⟩
  have hFuncΘ : Θ ≤ is_function η omega f := by
    dsimp [Θ, Δ]
    exact inf_le_left.trans (inf_le_left.trans hFunc)
  have hRel := (mem_induced_epsilon_rel_iff hFuncΘ).mp hPairMem
  apply (le_inf le_rfl hRel.2.2).trans
  apply lattice.bv_cases_right
  intro a'
  let Ω : 𝔹 := Θ ⊓ (a' ∈ᴮ η ⊓
    ⨆ b' : bSet 𝔹, b' ∈ᴮ η ⊓
      (pair a' a ∈ᴮ f ⊓ pair b' b ∈ᴮ f ⊓ a' ∈ᴮ b'))
  change Ω ≤ ⊥
  have hCases : Ω ≤ ⨆ b' : bSet 𝔹, b' ∈ᴮ η ⊓
      (pair a' a ∈ᴮ f ⊓ pair b' b ∈ᴮ f ⊓ a' ∈ᴮ b') := by
    dsimp [Ω]
    exact inf_le_right.trans inf_le_right
  apply (le_inf le_rfl hCases).trans
  apply lattice.bv_cases_right
  intro b'
  let Ξ : 𝔹 := Ω ⊓ (b' ∈ᴮ η ⊓
    (pair a' a ∈ᴮ f ⊓ pair b' b ∈ᴮ f ⊓ a' ∈ᴮ b'))
  change Ξ ≤ ⊥
  have hΞΘ : Ξ ≤ Θ := by
    dsimp [Ξ, Ω]
    exact inf_le_left.trans inf_le_left
  have hEqOne : Ξ ≤ η =ᴮ (1 : bSet 𝔹) := by
    dsimp [Ξ, Ω, Θ, Δ]
    exact inf_le_left.trans (inf_le_left.trans (inf_le_left.trans inf_le_right))
  have hFuncΞ : Ξ ≤ is_function η omega f :=
    hΞΘ.trans hFuncΘ
  have hf₁ : Ξ ≤ pair a' a ∈ᴮ f := by
    dsimp [Ξ]
    exact inf_le_right.trans inf_le_right |>.trans (inf_le_left.trans inf_le_left)
  have hf₂ : Ξ ≤ pair b' b ∈ᴮ f := by
    dsimp [Ξ]
    exact inf_le_right.trans inf_le_right |>.trans (inf_le_left.trans inf_le_right)
  have ha'b' : Ξ ≤ a' ∈ᴮ b' := by
    dsimp [Ξ]
    exact inf_le_right.trans inf_le_right |>.trans inf_le_right
  have ha'One : Ξ ≤ a' ∈ᴮ (1 : bSet 𝔹) :=
    subst_congr_mem_right' hEqOne (mem_domain_of_is_function hf₁ hFuncΞ)
  have hb'One : Ξ ≤ b' ∈ᴮ (1 : bSet 𝔹) :=
    subst_congr_mem_right' hEqOne (mem_domain_of_is_function hf₂ hFuncΞ)
  have ha'Zero : Ξ ≤ a' =ᴮ (0 : bSet 𝔹) :=
    eq_zero_of_mem_one ha'One
  have hb'Zero : Ξ ≤ b' =ᴮ (0 : bSet 𝔹) :=
    eq_zero_of_mem_one hb'One
  have hZeroMemB' : Ξ ≤ (0 : bSet 𝔹) ∈ᴮ b' :=
    subst_congr_mem_left' ha'Zero ha'b'
  have hZeroMemZero : Ξ ≤ (0 : bSet 𝔹) ∈ᴮ (0 : bSet 𝔹) :=
    subst_congr_mem_right' hb'Zero hZeroMemB'
  exact bot_of_mem_self hZeroMemZero

lemma nonempty_induced_rel_iff_not_zero_and_not_one {η f : bSet 𝔹} {Γ : 𝔹}
    (hOrd : Γ ≤ Ord η) (hFunc : Γ ≤ is_function η omega f) :
    Γ ≤ (induced_epsilon_rel η omega f =ᴮ ∅)ᶜ ↔
      Γ ≤ (η =ᴮ (0 : bSet 𝔹))ᶜ ∧ Γ ≤ (η =ᴮ (1 : bSet 𝔹))ᶜ := by
  constructor
  · intro hNonempty
    exact ⟨not_zero_of_induced_rel_nonempty hFunc hNonempty,
      not_one_of_induced_rel_nonempty hFunc hNonempty⟩
  · rintro ⟨hNotZero, hNotOne⟩
    rw [nonempty_iff_exists_mem]
    have hOneη : Γ ≤ (1 : bSet 𝔹) ∈ᴮ η :=
      one_mem_of_not_zero_and_not_one hOrd hNotZero hNotOne
    have hZeroη : Γ ≤ (0 : bSet 𝔹) ∈ᴮ η :=
      mem_of_mem_Ord zero_mem_one hOneη hOrd
    have hTotalZero : Γ ≤
        ⨆ a : bSet 𝔹, a ∈ᴮ omega ⊓ pair (0 : bSet 𝔹) a ∈ᴮ f := by
      have hImp : Γ ≤ lattice.imp ((0 : bSet 𝔹) ∈ᴮ η)
          (⨆ a : bSet 𝔹, a ∈ᴮ omega ⊓ pair (0 : bSet 𝔹) a ∈ᴮ f) :=
        (is_total_of_is_function hFunc).trans (iInf_le _ (0 : bSet 𝔹))
      exact lattice.bv_context_apply hImp hZeroη
    apply (le_inf le_rfl hTotalZero).trans
    apply lattice.bv_cases_right
    intro a
    let Δ : 𝔹 := Γ ⊓ (a ∈ᴮ omega ⊓ pair (0 : bSet 𝔹) a ∈ᴮ f)
    change Δ ≤ ⨆ pr : bSet 𝔹, pr ∈ᴮ induced_epsilon_rel η omega f
    have hAω : Δ ≤ a ∈ᴮ omega := by
      dsimp [Δ]
      exact inf_le_right.trans inf_le_left
    have hPairZeroA : Δ ≤ pair (0 : bSet 𝔹) a ∈ᴮ f := by
      dsimp [Δ]
      exact inf_le_right.trans inf_le_right
    have hOneηΔ : Δ ≤ (1 : bSet 𝔹) ∈ᴮ η :=
      inf_le_left.trans hOneη
    have hTotalOne : Δ ≤
        ⨆ b : bSet 𝔹, b ∈ᴮ omega ⊓ pair (1 : bSet 𝔹) b ∈ᴮ f := by
      have hImp : Δ ≤ lattice.imp ((1 : bSet 𝔹) ∈ᴮ η)
          (⨆ b : bSet 𝔹, b ∈ᴮ omega ⊓ pair (1 : bSet 𝔹) b ∈ᴮ f) :=
        (inf_le_left.trans (is_total_of_is_function hFunc)).trans (iInf_le _ (1 : bSet 𝔹))
      exact lattice.bv_context_apply hImp hOneηΔ
    apply (le_inf le_rfl hTotalOne).trans
    apply lattice.bv_cases_right
    intro b
    let Θ : 𝔹 := Δ ⊓ (b ∈ᴮ omega ⊓ pair (1 : bSet 𝔹) b ∈ᴮ f)
    change Θ ≤ ⨆ pr : bSet 𝔹, pr ∈ᴮ induced_epsilon_rel η omega f
    apply lattice.bv_use (pair a b)
    have hFuncΘ : Θ ≤ is_function η omega f := by
      dsimp [Θ, Δ]
      exact inf_le_left.trans (inf_le_left.trans hFunc)
    apply (mem_induced_epsilon_rel_iff hFuncΘ).mpr
    refine ⟨?_, ?_, ?_⟩
    · exact inf_le_left.trans hAω
    · dsimp [Θ]
      exact inf_le_right.trans inf_le_left
    · apply lattice.bv_use (0 : bSet 𝔹)
      apply le_inf
      · dsimp [Θ, Δ]
        exact inf_le_left.trans (inf_le_left.trans hZeroη)
      · apply lattice.bv_use (1 : bSet 𝔹)
        apply le_inf
        · dsimp [Θ, Δ]
          exact inf_le_left.trans (inf_le_left.trans hOneη)
        · apply le_inf
          · apply le_inf
            · exact inf_le_left.trans hPairZeroA
            · dsimp [Θ]
              exact inf_le_right.trans inf_le_right
          · exact zero_mem_one

lemma image_eq_of_eq_induced_epsilon_rel_aux {η ρ f g : bSet 𝔹} {Γ : 𝔹}
    (hηInj : Γ ≤ is_injective_function η omega f)
    (hρInj : Γ ≤ is_injective_function ρ omega g)
    (hEq : Γ ≤ induced_epsilon_rel η omega f =ᴮ induced_epsilon_rel ρ omega g)
    (hExistsTwo : Γ ≤ exists_two η) :
    Γ ≤ ⨅ z : bSet 𝔹, (z ∈ᴮ image η omega f) ⟹ (z ∈ᴮ image ρ omega g) := by
  apply le_iInf
  intro z
  apply lattice.bv_imp_intro
  let Δ : 𝔹 := Γ ⊓ z ∈ᴮ image η omega f
  change Δ ≤ z ∈ᴮ image ρ omega g
  have hImg := (mem_image_iff (x := η) (y := omega) (b := z) (f := f) (Γ := Δ)).mp
    inf_le_right
  have hzOmega : Δ ≤ z ∈ᴮ omega := hImg.1
  have hPreimage : Δ ≤ ⨆ z' : bSet 𝔹, z' ∈ᴮ η ⊓ pair z' z ∈ᴮ f := hImg.2
  apply (le_inf le_rfl hPreimage).trans
  apply lattice.bv_cases_right
  intro z'
  let Θ : 𝔹 := Δ ⊓ (z' ∈ᴮ η ⊓ pair z' z ∈ᴮ f)
  change Θ ≤ z ∈ᴮ image ρ omega g
  have hz'η : Θ ≤ z' ∈ᴮ η := by
    dsimp [Θ]
    exact inf_le_right.trans inf_le_left
  have hz'zF : Θ ≤ pair z' z ∈ᴮ f := by
    dsimp [Θ]
    exact inf_le_right.trans inf_le_right
  have hΘΓ : Θ ≤ Γ := by
    dsimp [Θ, Δ]
    exact inf_le_left.trans inf_le_left
  have hExistsImp : Θ ≤ lattice.imp (z' ∈ᴮ η)
      (⨆ w' : bSet 𝔹, w' ∈ᴮ η ⊓ (z' ∈ᴮ w' ⊔ w' ∈ᴮ z')) :=
    (hΘΓ.trans hExistsTwo).trans (iInf_le _ z')
  have hWitness : Θ ≤ ⨆ w' : bSet 𝔹, w' ∈ᴮ η ⊓ (z' ∈ᴮ w' ⊔ w' ∈ᴮ z') :=
    lattice.bv_context_apply hExistsImp hz'η
  apply (le_inf le_rfl hWitness).trans
  apply lattice.bv_cases_right
  intro w'
  let Λ : 𝔹 := Θ ⊓ (w' ∈ᴮ η ⊓ (z' ∈ᴮ w' ⊔ w' ∈ᴮ z'))
  change Λ ≤ z ∈ᴮ image ρ omega g
  have hw'η : Λ ≤ w' ∈ᴮ η := by
    dsimp [Λ]
    exact inf_le_right.trans inf_le_left
  have hRelCases : Λ ≤ z' ∈ᴮ w' ⊔ w' ∈ᴮ z' := by
    dsimp [Λ]
    exact inf_le_right.trans inf_le_right
  have hΛΓ : Λ ≤ Γ := by
    dsimp [Λ]
    exact inf_le_left.trans hΘΓ
  have hFuncη : Λ ≤ is_function η omega f :=
    is_function_of_is_injective_function (hΛΓ.trans hηInj)
  have hTotalImp : Λ ≤ lattice.imp (w' ∈ᴮ η)
      (⨆ w : bSet 𝔹, w ∈ᴮ omega ⊓ pair w' w ∈ᴮ f) :=
    (is_total_of_is_function hFuncη).trans (iInf_le _ w')
  have hImageW : Λ ≤ ⨆ w : bSet 𝔹, w ∈ᴮ omega ⊓ pair w' w ∈ᴮ f :=
    lattice.bv_context_apply hTotalImp hw'η
  apply (le_inf le_rfl hImageW).trans
  apply lattice.bv_cases_right
  intro w
  let Ω : 𝔹 := Λ ⊓ (w ∈ᴮ omega ⊓ pair w' w ∈ᴮ f)
  change Ω ≤ z ∈ᴮ image ρ omega g
  have hwOmega : Ω ≤ w ∈ᴮ omega := by
    dsimp [Ω]
    exact inf_le_right.trans inf_le_left
  have hw'wF : Ω ≤ pair w' w ∈ᴮ f := by
    dsimp [Ω]
    exact inf_le_right.trans inf_le_right
  have hzOmegaΩ : Ω ≤ z ∈ᴮ omega :=
    inf_le_left.trans (inf_le_left.trans (inf_le_left.trans hzOmega))
  have hΩΓ : Ω ≤ Γ := by
    dsimp [Ω]
    exact inf_le_left.trans hΛΓ
  have hρFunc : Ω ≤ is_function ρ omega g :=
    is_function_of_is_injective_function (hΩΓ.trans hρInj)
  apply (le_inf le_rfl (inf_le_left.trans hRelCases)).trans
  apply lattice.bv_or_elim_right
  · have hzMemIndη : Ω ⊓ z' ∈ᴮ w' ≤
        pair z w ∈ᴮ induced_epsilon_rel η omega f := by
      have hFuncη' : Ω ⊓ z' ∈ᴮ w' ≤ is_function η omega f :=
        is_function_of_is_injective_function ((inf_le_left.trans hΩΓ).trans hηInj)
      apply (mem_induced_epsilon_rel_iff hFuncη').mpr
      refine ⟨inf_le_left.trans hzOmegaΩ, inf_le_left.trans hwOmega, ?_⟩
      apply lattice.bv_use z'
      apply le_inf
      · exact inf_le_left.trans (inf_le_left.trans (inf_le_left.trans hz'η))
      · apply lattice.bv_use w'
        apply le_inf
        · exact inf_le_left.trans (inf_le_left.trans hw'η)
        · exact le_inf
            (le_inf
              (inf_le_left.trans (inf_le_left.trans (inf_le_left.trans hz'zF)))
              (inf_le_left.trans hw'wF))
            inf_le_right
    have hzMemIndρ : Ω ⊓ z' ∈ᴮ w' ≤
        pair z w ∈ᴮ induced_epsilon_rel ρ omega g :=
      subst_congr_mem_right' ((inf_le_left.trans hΩΓ).trans hEq) hzMemIndη
    exact induced_epsilon_rel_sub_image_left (inf_le_left.trans hρFunc) hzMemIndρ
  · have hwMemIndη : Ω ⊓ w' ∈ᴮ z' ≤
        pair w z ∈ᴮ induced_epsilon_rel η omega f := by
      have hFuncη' : Ω ⊓ w' ∈ᴮ z' ≤ is_function η omega f :=
        is_function_of_is_injective_function ((inf_le_left.trans hΩΓ).trans hηInj)
      apply (mem_induced_epsilon_rel_iff hFuncη').mpr
      refine ⟨inf_le_left.trans hwOmega, inf_le_left.trans hzOmegaΩ, ?_⟩
      apply lattice.bv_use w'
      apply le_inf
      · exact inf_le_left.trans (inf_le_left.trans hw'η)
      · apply lattice.bv_use z'
        apply le_inf
        · exact inf_le_left.trans (inf_le_left.trans (inf_le_left.trans hz'η))
        · exact le_inf
            (le_inf (inf_le_left.trans hw'wF)
              (inf_le_left.trans (inf_le_left.trans (inf_le_left.trans hz'zF))))
            inf_le_right
    have hwMemIndρ : Ω ⊓ w' ∈ᴮ z' ≤
        pair w z ∈ᴮ induced_epsilon_rel ρ omega g :=
      subst_congr_mem_right' ((inf_le_left.trans hΩΓ).trans hEq) hwMemIndη
    exact induced_epsilon_rel_sub_image_right (inf_le_left.trans hρFunc) hwMemIndρ

lemma image_eq_of_eq_induced_epsilon_rel {η ρ f g : bSet 𝔹} {Γ : 𝔹}
    (hηInj : Γ ≤ is_injective_function η omega f)
    (hρInj : Γ ≤ is_injective_function ρ omega g)
    (hEq : Γ ≤ induced_epsilon_rel η omega f =ᴮ induced_epsilon_rel ρ omega g)
    (hExistsTwoη : Γ ≤ exists_two η) (hExistsTwoρ : Γ ≤ exists_two ρ) :
    Γ ≤ image η omega f =ᴮ image ρ omega g := by
  apply mem_ext
  · exact image_eq_of_eq_induced_epsilon_rel_aux hηInj hρInj hEq hExistsTwoη
  · exact image_eq_of_eq_induced_epsilon_rel_aux hρInj hηInj (bv_symm hEq) hExistsTwoρ

def induced_epsilon_comp {η ρ f g : bSet 𝔹} {Γ : 𝔹}
    (hηInj : Γ ≤ is_injective_function η omega f)
    (hρInj : Γ ≤ is_injective_function ρ omega g)
    (hEq : Γ ≤ induced_epsilon_rel η omega f =ᴮ induced_epsilon_rel ρ omega g)
    (hExistsTwoη : Γ ≤ exists_two η) (hExistsTwoρ : Γ ≤ exists_two ρ) : bSet 𝔹 :=
  let hImgEq : Γ ≤ image η omega f =ᴮ image ρ omega g :=
    image_eq_of_eq_induced_epsilon_rel hηInj hρInj hEq hExistsTwoη hExistsTwoρ
  let hηToImgρ : Γ ≤ is_injective_function η (image ρ omega g) f :=
    is_injective_function_codomain_congr hImgEq (factor_image_is_injective_function hηInj)
  let hρInv : Γ ≤ is_injective_function (image ρ omega g) ρ
      (injective_function_inverse hρInj) :=
    injective_function_inverse_is_injective_function (hInj := hρInj)
  injective_function_comp hηToImgρ hρInv

lemma induced_epsilon_comp_is_function {η ρ f g : bSet 𝔹} {Γ : 𝔹}
    (hηInj : Γ ≤ is_injective_function η omega f)
    (hρInj : Γ ≤ is_injective_function ρ omega g)
    (hEq : Γ ≤ induced_epsilon_rel η omega f =ᴮ induced_epsilon_rel ρ omega g)
    (hExistsTwoη : Γ ≤ exists_two η) (hExistsTwoρ : Γ ≤ exists_two ρ) :
    Γ ≤ is_function η ρ
      (induced_epsilon_comp hηInj hρInj hEq hExistsTwoη hExistsTwoρ) := by
  unfold induced_epsilon_comp
  exact injective_function_comp_is_function

lemma induced_epsilon_comp_is_surj {η ρ f g : bSet 𝔹} {Γ : 𝔹}
    (hηInj : Γ ≤ is_injective_function η omega f)
    (hρInj : Γ ≤ is_injective_function ρ omega g)
    (hEq : Γ ≤ induced_epsilon_rel η omega f =ᴮ induced_epsilon_rel ρ omega g)
    (hExistsTwoη : Γ ≤ exists_two η) (hExistsTwoρ : Γ ≤ exists_two ρ) :
    Γ ≤ is_surj η ρ
      (induced_epsilon_comp hηInj hρInj hEq hExistsTwoη hExistsTwoρ) := by
  unfold induced_epsilon_comp
  let hImgEq : Γ ≤ image η omega f =ᴮ image ρ omega g :=
    image_eq_of_eq_induced_epsilon_rel hηInj hρInj hEq hExistsTwoη hExistsTwoρ
  let hηToImgρ : Γ ≤ is_injective_function η (image ρ omega g) f :=
    is_injective_function_codomain_congr hImgEq (factor_image_is_injective_function hηInj)
  let hρInv : Γ ≤ is_injective_function (image ρ omega g) ρ
      (injective_function_inverse hρInj) :=
    injective_function_inverse_is_injective_function (hInj := hρInj)
  have hSurjηImageη : Γ ≤ is_surj η (image η omega f) f :=
    surj_image (is_func'_of_is_injective_function hηInj)
  have hSurjηImageρ : Γ ≤ is_surj η (image ρ omega g) f :=
    is_surj_codomain_congr hImgEq hSurjηImageη
  have hSurjInv : Γ ≤ is_surj (image ρ omega g) ρ (injective_function_inverse hρInj) := by
    simpa [injective_function_inverse] using
      inj_inverse_is_surj (is_func'_of_is_injective_function hρInj)
        (is_inj_of_is_injective_function hρInj)
  simpa [injective_function_comp] using
    is_func'_comp_surj
      (is_func'_of_is_injective_function hηToImgρ)
      (is_func'_of_is_injective_function hρInv)
      hSurjηImageρ hSurjInv

lemma induced_epsilon_comp_strong_eps_hom {η ρ f g : bSet 𝔹} {Γ : 𝔹}
    (hηInj : Γ ≤ is_injective_function η omega f)
    (hρInj : Γ ≤ is_injective_function ρ omega g)
    (hEq : Γ ≤ induced_epsilon_rel η omega f =ᴮ induced_epsilon_rel ρ omega g)
    (hExistsTwoη : Γ ≤ exists_two η) (hExistsTwoρ : Γ ≤ exists_two ρ) :
    Γ ≤ strong_eps_hom η ρ
      (induced_epsilon_comp hηInj hρInj hEq hExistsTwoη hExistsTwoρ) := by
  rw [strong_eps_hom_iff]
  intro Γ' hΓ'Γ z₁ hz₁ z₂ hz₂ w₁ hw₁ w₂ hw₂ hpr₁ hpr₂
  let hImgEq : Γ ≤ image η omega f =ᴮ image ρ omega g :=
    image_eq_of_eq_induced_epsilon_rel hηInj hρInj hEq hExistsTwoη hExistsTwoρ
  let hηToImgρ : Γ ≤ is_injective_function η (image ρ omega g) f :=
    is_injective_function_codomain_congr hImgEq (factor_image_is_injective_function hηInj)
  let hρInv : Γ ≤ is_injective_function (image ρ omega g) ρ
      (injective_function_inverse hρInj) :=
    injective_function_inverse_is_injective_function (hInj := hρInj)
  have hpr₁Comp : Γ' ≤ pair z₁ w₁ ∈ᴮ
      is_func'_comp (is_func'_of_is_injective_function hηToImgρ)
        (is_func'_of_is_injective_function hρInv) := by
    simpa [induced_epsilon_comp, injective_function_comp] using hpr₁
  have hpr₂Comp : Γ' ≤ pair z₂ w₂ ∈ᴮ
      is_func'_comp (is_func'_of_is_injective_function hηToImgρ)
        (is_func'_of_is_injective_function hρInv) := by
    simpa [induced_epsilon_comp, injective_function_comp] using hpr₂
  have hInfo₁ := (mem_is_func'_comp_iff
    (hF := is_func'_of_is_injective_function hηToImgρ)
    (hG := is_func'_of_is_injective_function hρInv)
    (a := z₁) (c := w₁)).mp hpr₁Comp
  have hInfo₂ := (mem_is_func'_comp_iff
    (hF := is_func'_of_is_injective_function hηToImgρ)
    (hG := is_func'_of_is_injective_function hρInv)
    (a := z₂) (c := w₂)).mp hpr₂Comp
  constructor
  · intro hzMem
    apply (le_inf le_rfl hInfo₁.2.2).trans
    apply lattice.bv_cases_right
    intro v₁
    let Δ : 𝔹 := Γ' ⊓ (v₁ ∈ᴮ image ρ omega g ⊓
      (pair z₁ v₁ ∈ᴮ f ⊓ pair v₁ w₁ ∈ᴮ injective_function_inverse hρInj))
    change Δ ≤ w₁ ∈ᴮ w₂
    have hInfo₂Δ : Δ ≤ ⨆ v₂ : bSet 𝔹, v₂ ∈ᴮ image ρ omega g ⊓
        (pair z₂ v₂ ∈ᴮ f ⊓ pair v₂ w₂ ∈ᴮ injective_function_inverse hρInj) :=
      inf_le_left.trans hInfo₂.2.2
    apply (le_inf le_rfl hInfo₂Δ).trans
    apply lattice.bv_cases_right
    intro v₂
    let Θ : 𝔹 := Δ ⊓ (v₂ ∈ᴮ image ρ omega g ⊓
      (pair z₂ v₂ ∈ᴮ f ⊓ pair v₂ w₂ ∈ᴮ injective_function_inverse hρInj))
    change Θ ≤ w₁ ∈ᴮ w₂
    have hΘΓ' : Θ ≤ Γ' := by
      dsimp [Θ, Δ]
      exact inf_le_left.trans inf_le_left
    have hΘΓ : Θ ≤ Γ := hΘΓ'.trans hΓ'Γ
    have hz₁Θ : Θ ≤ z₁ ∈ᴮ η := hΘΓ'.trans hz₁
    have hz₂Θ : Θ ≤ z₂ ∈ᴮ η := hΘΓ'.trans hz₂
    have hzMemΘ : Θ ≤ z₁ ∈ᴮ z₂ := hΘΓ'.trans hzMem
    have hz₁v₁F : Θ ≤ pair z₁ v₁ ∈ᴮ f := by
      dsimp [Θ, Δ]
      exact inf_le_left.trans (inf_le_right.trans inf_le_right |>.trans inf_le_left)
    have hv₁w₁Inv : Θ ≤ pair v₁ w₁ ∈ᴮ injective_function_inverse hρInj := by
      dsimp [Θ, Δ]
      exact inf_le_left.trans (inf_le_right.trans inf_le_right |>.trans inf_le_right)
    have hz₂v₂F : Θ ≤ pair z₂ v₂ ∈ᴮ f := by
      dsimp [Θ]
      exact inf_le_right.trans inf_le_right |>.trans inf_le_left
    have hv₂w₂Inv : Θ ≤ pair v₂ w₂ ∈ᴮ injective_function_inverse hρInj := by
      dsimp [Θ]
      exact inf_le_right.trans inf_le_right |>.trans inf_le_right
    have hv₁w₁Inv' : Θ ≤ pair v₁ w₁ ∈ᴮ
        inj_inverse (is_func'_of_is_injective_function hρInj)
          (is_inj_of_is_injective_function hρInj) := by
      simpa [injective_function_inverse] using hv₁w₁Inv
    have hv₂w₂Inv' : Θ ≤ pair v₂ w₂ ∈ᴮ
        inj_inverse (is_func'_of_is_injective_function hρInj)
          (is_inj_of_is_injective_function hρInj) := by
      simpa [injective_function_inverse] using hv₂w₂Inv
    have hInv₁ := (mem_inj_inverse_iff
      (hFunc := is_func'_of_is_injective_function hρInj)
      (hInj := is_inj_of_is_injective_function hρInj)
      (b := v₁) (a := w₁)).mp hv₁w₁Inv'
    have hInv₂ := (mem_inj_inverse_iff
      (hFunc := is_func'_of_is_injective_function hρInj)
      (hInj := is_inj_of_is_injective_function hρInj)
      (b := v₂) (a := w₂)).mp hv₂w₂Inv'
    have hFuncη : Θ ≤ is_function η omega f :=
      hΘΓ.trans (is_function_of_is_injective_function hηInj)
    have hvRelη : Θ ≤ pair v₁ v₂ ∈ᴮ induced_epsilon_rel η omega f := by
      apply (mem_induced_epsilon_rel_iff hFuncη).mpr
      refine ⟨hInv₁.2.1, hInv₂.2.1, ?_⟩
      apply lattice.bv_use z₁
      apply le_inf
      · exact hz₁Θ
      · apply lattice.bv_use z₂
        exact le_inf hz₂Θ (le_inf (le_inf hz₁v₁F hz₂v₂F) hzMemΘ)
    have hvRelρ : Θ ≤ pair v₁ v₂ ∈ᴮ induced_epsilon_rel ρ omega g :=
      subst_congr_mem_right' (hΘΓ.trans hEq) hvRelη
    exact mem_of_mem_induced_epsilon_rel (hΘΓ.trans hρInj) hInv₁.2.2 hInv₂.2.2 hvRelρ
  · intro hwMem
    apply (le_inf le_rfl hInfo₁.2.2).trans
    apply lattice.bv_cases_right
    intro v₁
    let Δ : 𝔹 := Γ' ⊓ (v₁ ∈ᴮ image ρ omega g ⊓
      (pair z₁ v₁ ∈ᴮ f ⊓ pair v₁ w₁ ∈ᴮ injective_function_inverse hρInj))
    change Δ ≤ z₁ ∈ᴮ z₂
    have hInfo₂Δ : Δ ≤ ⨆ v₂ : bSet 𝔹, v₂ ∈ᴮ image ρ omega g ⊓
        (pair z₂ v₂ ∈ᴮ f ⊓ pair v₂ w₂ ∈ᴮ injective_function_inverse hρInj) :=
      inf_le_left.trans hInfo₂.2.2
    apply (le_inf le_rfl hInfo₂Δ).trans
    apply lattice.bv_cases_right
    intro v₂
    let Θ : 𝔹 := Δ ⊓ (v₂ ∈ᴮ image ρ omega g ⊓
      (pair z₂ v₂ ∈ᴮ f ⊓ pair v₂ w₂ ∈ᴮ injective_function_inverse hρInj))
    change Θ ≤ z₁ ∈ᴮ z₂
    have hΘΓ' : Θ ≤ Γ' := by
      dsimp [Θ, Δ]
      exact inf_le_left.trans inf_le_left
    have hΘΓ : Θ ≤ Γ := hΘΓ'.trans hΓ'Γ
    have hwMemΘ : Θ ≤ w₁ ∈ᴮ w₂ := hΘΓ'.trans hwMem
    have hz₁v₁F : Θ ≤ pair z₁ v₁ ∈ᴮ f := by
      dsimp [Θ, Δ]
      exact inf_le_left.trans (inf_le_right.trans inf_le_right |>.trans inf_le_left)
    have hv₁w₁Inv : Θ ≤ pair v₁ w₁ ∈ᴮ injective_function_inverse hρInj := by
      dsimp [Θ, Δ]
      exact inf_le_left.trans (inf_le_right.trans inf_le_right |>.trans inf_le_right)
    have hz₂v₂F : Θ ≤ pair z₂ v₂ ∈ᴮ f := by
      dsimp [Θ]
      exact inf_le_right.trans inf_le_right |>.trans inf_le_left
    have hv₂w₂Inv : Θ ≤ pair v₂ w₂ ∈ᴮ injective_function_inverse hρInj := by
      dsimp [Θ]
      exact inf_le_right.trans inf_le_right |>.trans inf_le_right
    have hv₁w₁Inv' : Θ ≤ pair v₁ w₁ ∈ᴮ
        inj_inverse (is_func'_of_is_injective_function hρInj)
          (is_inj_of_is_injective_function hρInj) := by
      simpa [injective_function_inverse] using hv₁w₁Inv
    have hv₂w₂Inv' : Θ ≤ pair v₂ w₂ ∈ᴮ
        inj_inverse (is_func'_of_is_injective_function hρInj)
          (is_inj_of_is_injective_function hρInj) := by
      simpa [injective_function_inverse] using hv₂w₂Inv
    have hInv₁ := (mem_inj_inverse_iff
      (hFunc := is_func'_of_is_injective_function hρInj)
      (hInj := is_inj_of_is_injective_function hρInj)
      (b := v₁) (a := w₁)).mp hv₁w₁Inv'
    have hInv₂ := (mem_inj_inverse_iff
      (hFunc := is_func'_of_is_injective_function hρInj)
      (hInj := is_inj_of_is_injective_function hρInj)
      (b := v₂) (a := w₂)).mp hv₂w₂Inv'
    have hFuncρ : Θ ≤ is_function ρ omega g :=
      hΘΓ.trans (is_function_of_is_injective_function hρInj)
    have hvRelρ : Θ ≤ pair v₁ v₂ ∈ᴮ induced_epsilon_rel ρ omega g := by
      apply (mem_induced_epsilon_rel_iff hFuncρ).mpr
      refine ⟨hInv₁.2.1, hInv₂.2.1, ?_⟩
      apply lattice.bv_use w₁
      apply le_inf
      · exact hInv₁.1
      · apply lattice.bv_use w₂
        exact le_inf hInv₂.1 (le_inf (le_inf hInv₁.2.2 hInv₂.2.2) hwMemΘ)
    have hvRelη : Θ ≤ pair v₁ v₂ ∈ᴮ induced_epsilon_rel η omega f :=
      subst_congr_mem_right' (bv_symm (hΘΓ.trans hEq)) hvRelρ
    exact mem_of_mem_induced_epsilon_rel (hΘΓ.trans hηInj) hz₁v₁F hz₂v₂F hvRelη

lemma induced_epsilon_comp_eps_iso {η ρ f g : bSet 𝔹} {Γ : 𝔹}
    (hηInj : Γ ≤ is_injective_function η omega f)
    (hρInj : Γ ≤ is_injective_function ρ omega g)
    (hEq : Γ ≤ induced_epsilon_rel η omega f =ᴮ induced_epsilon_rel ρ omega g)
    (hExistsTwoη : Γ ≤ exists_two η) (hExistsTwoρ : Γ ≤ exists_two ρ) :
    Γ ≤ eps_iso η ρ
      (induced_epsilon_comp hηInj hρInj hEq hExistsTwoη hExistsTwoρ) := by
  unfold eps_iso
  exact le_inf
    (le_inf
      (induced_epsilon_comp_is_function hηInj hρInj hEq hExistsTwoη hExistsTwoρ)
      (induced_epsilon_comp_strong_eps_hom hηInj hρInj hEq hExistsTwoη hExistsTwoρ))
    (induced_epsilon_comp_is_surj hηInj hρInj hEq hExistsTwoη hExistsTwoρ)

lemma eq_of_eq_induced_epsilon_rel {η ρ f g : bSet 𝔹} {Γ : 𝔹}
    (hηOrd : Γ ≤ Ord η) (hρOrd : Γ ≤ Ord ρ)
    (hηInj : Γ ≤ is_injective_function η omega f)
    (hρInj : Γ ≤ is_injective_function ρ omega g)
    (hEq : Γ ≤ induced_epsilon_rel η omega f =ᴮ induced_epsilon_rel ρ omega g)
    (hExistsTwoη : Γ ≤ exists_two η) (hExistsTwoρ : Γ ≤ exists_two ρ) :
    Γ ≤ η =ᴮ ρ := by
  apply eq_of_Ord_eps_iso hηOrd hρOrd
  apply lattice.bv_use
    (induced_epsilon_comp hηInj hρInj hEq hExistsTwoη hExistsTwoρ)
  exact induced_epsilon_comp_eps_iso hηInj hρInj hEq hExistsTwoη hExistsTwoρ

lemma B_ext_induced_epsilon_rel_eq_right (v f : bSet 𝔹) :
    B_ext (fun x : bSet 𝔹 => induced_epsilon_rel x omega f =ᴮ v) := by
  intro x y
  let Γ : 𝔹 := x =ᴮ y ⊓ (induced_epsilon_rel x omega f =ᴮ v)
  change Γ ≤ induced_epsilon_rel y omega f =ᴮ v
  have hxy : Γ ≤ x =ᴮ y := inf_le_left
  have hEqV : Γ ≤ induced_epsilon_rel x omega f =ᴮ v := inf_le_right
  have hRel : Γ ≤ mem_rel x =ᴮ mem_rel y :=
    hxy.trans (B_congr_mem_rel x y)
  have hImageRel : Γ ≤
      image (mem_rel x) (prod omega omega) (prod.map_self x omega f) =ᴮ
        image (mem_rel y) (prod omega omega) (prod.map_self x omega f) :=
    hRel.trans (B_congr_image_left (prod omega omega) (prod.map_self x omega f)
      (mem_rel x) (mem_rel y))
  have hMap : Γ ≤ prod.map_self x omega f =ᴮ prod.map_self y omega f :=
    hxy.trans (B_congr_prod_map_self_left (y := omega) (f := f) x y)
  have hImageMap : Γ ≤
      image (mem_rel y) (prod omega omega) (prod.map_self x omega f) =ᴮ
        image (mem_rel y) (prod omega omega) (prod.map_self y omega f) :=
    hMap.trans (B_congr_image_right (mem_rel y) (prod omega omega)
      (prod.map_self x omega f) (prod.map_self y omega f))
  have hCongr : Γ ≤ induced_epsilon_rel x omega f =ᴮ induced_epsilon_rel y omega f := by
    unfold induced_epsilon_rel
    exact bv_trans hImageRel hImageMap
  exact bv_trans (bv_symm hCongr) hEqV

namespace a1

/-- Predicate selecting nonempty pushforwards of ordinal epsilon relations into `omega × omega`. -/
def ϕ (x : bSet 𝔹) : 𝔹 :=
  ⨆ η : bSet 𝔹, Ord η ⊓
    ⨆ f : bSet 𝔹, is_injective_function η omega f ⊓
      (induced_epsilon_rel η omega f =ᴮ x) ⊓ (x =ᴮ ∅)ᶜ

lemma B_ext_ϕ : B_ext (ϕ : bSet 𝔹 → 𝔹) := by
  unfold ϕ
  apply B_ext_iSup
  intro η
  apply B_ext_inf
  · exact B_ext_const (Ord η)
  · apply B_ext_iSup
    intro f
    apply B_ext_inf
    · apply B_ext_inf
      · exact B_ext_const (is_injective_function η omega f)
      · exact B_ext_eq_right (induced_epsilon_rel η omega f)
    · exact B_ext_compl (B_ext_eq_left ∅)

/-- The ambient candidate set used by the upstream `a1` construction. -/
def candidates : bSet 𝔹 :=
  comprehend ϕ (bv_powerset (prod omega omega))

lemma mem_candidates_iff {x : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ x ∈ᴮ candidates ↔
      Γ ≤ ⨆ w : bSet 𝔹, w ∈ᴮ bv_powerset (prod omega omega) ⊓ (x =ᴮ w ⊓ ϕ w) := by
  simpa [candidates] using
    (mem_comprehend_iff₂ (𝔹 := 𝔹) (φ := ϕ) B_ext_ϕ (x := bv_powerset (prod omega omega))
      (z := x) (Γ := Γ))

/-- Predicate selecting an ordinal whose transported epsilon relation is a fixed code `v`. -/
def ψ (v : bSet 𝔹) (x : bSet 𝔹) : 𝔹 :=
  Ord x ⊓
    ⨆ f : bSet 𝔹, is_injective_function x omega f ⊓
      (induced_epsilon_rel x omega f =ᴮ v) ⊓ (v =ᴮ ∅)ᶜ

lemma B_ext_ψ {v : bSet 𝔹} : B_ext (ψ v : bSet 𝔹 → 𝔹) := by
  unfold ψ
  apply B_ext_inf
  · exact B_ext_Ord
  · apply B_ext_iSup
    intro f
    apply B_ext_inf
    · apply B_ext_inf
      · exact B_ext_is_injective_function_left (y := omega) (f := f)
      · exact B_ext_induced_epsilon_rel_eq_right v f
    · exact B_ext_const ((v =ᴮ ∅)ᶜ)

lemma candidates_AE {Γ : 𝔹} :
    Γ ≤ ⨅ z : bSet 𝔹, z ∈ᴮ candidates ⟹ ⨆ η : bSet 𝔹, ψ z η := by
  apply le_iInf
  intro z
  apply lattice.bv_imp_intro
  let Δ : 𝔹 := Γ ⊓ z ∈ᴮ candidates
  change Δ ≤ ⨆ η : bSet 𝔹, ψ z η
  have hzCases := (mem_candidates_iff (x := z) (Γ := Δ)).mp inf_le_right
  apply (le_inf le_rfl hzCases).trans
  apply lattice.bv_cases_right
  intro w
  let Θ : 𝔹 := Δ ⊓
    (w ∈ᴮ bv_powerset (prod omega omega) ⊓ (z =ᴮ w ⊓ ϕ w))
  have hzw : Θ ≤ z =ᴮ w := by
    dsimp [Θ]
    exact inf_le_right.trans inf_le_right |>.trans inf_le_left
  have hPhi : Θ ≤ ϕ w := by
    dsimp [Θ]
    exact inf_le_right.trans inf_le_right |>.trans inf_le_right
  unfold ϕ at hPhi
  apply (le_inf le_rfl hPhi).trans
  apply lattice.bv_cases_right
  intro η
  apply lattice.bv_use η
  unfold ψ
  apply le_inf
  · exact inf_le_right.trans inf_le_left
  · have hFsup : Θ ⊓ (Ord η ⊓
        ⨆ f : bSet 𝔹, is_injective_function η omega f ⊓
          (induced_epsilon_rel η omega f =ᴮ w) ⊓ (w =ᴮ ∅)ᶜ) ≤
        ⨆ f : bSet 𝔹, is_injective_function η omega f ⊓
          (induced_epsilon_rel η omega f =ᴮ w) ⊓ (w =ᴮ ∅)ᶜ :=
      inf_le_right.trans inf_le_right
    apply (le_inf le_rfl hFsup).trans
    apply lattice.bv_cases_right
    intro f
    apply lattice.bv_use f
    apply le_inf
    · apply le_inf
      · exact inf_le_right.trans inf_le_left |>.trans inf_le_left
      · have hIndW : Θ ⊓
            (Ord η ⊓ ⨆ f : bSet 𝔹, is_injective_function η omega f ⊓
              (induced_epsilon_rel η omega f =ᴮ w) ⊓ (w =ᴮ ∅)ᶜ) ⊓
            (is_injective_function η omega f ⊓
              (induced_epsilon_rel η omega f =ᴮ w) ⊓ (w =ᴮ ∅)ᶜ) ≤
            induced_epsilon_rel η omega f =ᴮ w :=
          inf_le_right.trans inf_le_left |>.trans inf_le_right
        have hEq : Θ ⊓
            (Ord η ⊓ ⨆ f : bSet 𝔹, is_injective_function η omega f ⊓
              (induced_epsilon_rel η omega f =ᴮ w) ⊓ (w =ᴮ ∅)ᶜ) ⊓
            (is_injective_function η omega f ⊓
              (induced_epsilon_rel η omega f =ᴮ w) ⊓ (w =ᴮ ∅)ᶜ) ≤ z =ᴮ w :=
          inf_le_left.trans inf_le_left |>.trans hzw
        exact bv_trans hIndW (bv_symm hEq)
    · have hNotW : Θ ⊓
          (Ord η ⊓ ⨆ f : bSet 𝔹, is_injective_function η omega f ⊓
            (induced_epsilon_rel η omega f =ᴮ w) ⊓ (w =ᴮ ∅)ᶜ) ⊓
          (is_injective_function η omega f ⊓
            (induced_epsilon_rel η omega f =ᴮ w) ⊓ (w =ᴮ ∅)ᶜ) ≤
          (w =ᴮ ∅)ᶜ :=
        inf_le_right.trans inf_le_right
      have hEq : Θ ⊓
          (Ord η ⊓ ⨆ f : bSet 𝔹, is_injective_function η omega f ⊓
            (induced_epsilon_rel η omega f =ᴮ w) ⊓ (w =ᴮ ∅)ᶜ) ⊓
          (is_injective_function η omega f ⊓
            (induced_epsilon_rel η omega f =ᴮ w) ⊓ (w =ᴮ ∅)ᶜ) ≤ w =ᴮ z :=
        bv_symm (inf_le_left.trans inf_le_left |>.trans hzw)
      exact (le_inf hEq hNotW).trans ((B_ext_compl (B_ext_eq_left ∅)) w z)

abbrev candidateType : Type u :=
  (candidates : bSet 𝔹).type

abbrev candidateBVal : candidateType (𝔹 := 𝔹) → 𝔹 :=
  (candidates : bSet 𝔹).bval

lemma func_exists (χ : candidateType (𝔹 := 𝔹)) :
    ∃ η : bSet 𝔹, candidates.bval χ ≤ ψ (candidates.func χ) η := by
  have hAll : candidates.bval χ ≤
      ⨅ z : bSet 𝔹, z ∈ᴮ candidates ⟹ ⨆ η : bSet 𝔹, ψ z η :=
    candidates_AE
  have hImp : candidates.bval χ ≤
      (candidates.func χ ∈ᴮ candidates ⟹ ⨆ η : bSet 𝔹, ψ (candidates.func χ) η) :=
    hAll.trans (iInf_le _ (candidates.func χ))
  have hMem : candidates.bval χ ≤ candidates.func χ ∈ᴮ candidates :=
    mem.mk'' le_rfl
  have hExists : candidates.bval χ ≤ ⨆ η : bSet 𝔹, ψ (candidates.func χ) η :=
    lattice.bv_context_apply hImp hMem
  exact exists_convert hExists B_ext_ψ

noncomputable def func (χ : candidateType (𝔹 := 𝔹)) : bSet 𝔹 :=
  Classical.choose (func_exists χ)

lemma func_spec {χ : candidateType (𝔹 := 𝔹)} {Γ : 𝔹}
    (hχ : Γ ≤ candidates.bval χ) :
    Γ ≤ ψ (candidates.func χ) (func χ) :=
  hχ.trans (Classical.choose_spec (func_exists χ))

noncomputable def aux : bSet 𝔹 :=
  ⟨candidateType, func, candidateBVal⟩

lemma Ord_of_mem_aux {Γ : 𝔹} {η : bSet 𝔹} (hMem : Γ ≤ η ∈ᴮ aux) :
    Γ ≤ Ord η := by
  rw [aux, mem_unfold] at hMem
  apply (le_inf le_rfl hMem).trans
  apply lattice.bv_cases_right
  intro χ
  let Δ : 𝔹 := Γ ⊓ (candidateBVal χ ⊓ η =ᴮ func χ)
  have hχVal : Δ ≤ candidates.bval χ := by
    dsimp [Δ, candidateBVal]
    exact inf_le_right.trans inf_le_left
  have hηEq : Δ ≤ η =ᴮ func χ := by
    dsimp [Δ]
    exact inf_le_right.trans inf_le_right
  have hSpec : Δ ≤ ψ (candidates.func χ) (func χ) :=
    func_spec hχVal
  have hOrdFunc : Δ ≤ Ord (func χ) := by
    unfold ψ at hSpec
    exact hSpec.trans inf_le_left
  exact (le_inf (bv_symm hηEq) hOrdFunc).trans (B_ext_Ord (func χ) η)

noncomputable def set : bSet 𝔹 :=
  insert (0 : bSet 𝔹) (insert (1 : bSet 𝔹) aux)

lemma Ord_of_mem_set {Γ : 𝔹} {η : bSet 𝔹} (hMem : Γ ≤ η ∈ᴮ set) :
    Γ ≤ Ord η := by
  rw [set, mem_insert1, mem_insert1] at hMem
  apply (le_inf le_rfl hMem).trans
  apply lattice.bv_or_elim_right
  · exact (le_inf (bv_symm inf_le_right) Ord_zero).trans (B_ext_Ord (0 : bSet 𝔹) η)
  · apply lattice.bv_or_elim_right
    · exact (le_inf (bv_symm inf_le_right) Ord_one).trans (B_ext_Ord (1 : bSet 𝔹) η)
    · exact Ord_of_mem_aux inf_le_right

end a1

noncomputable def a1 : bSet 𝔹 :=
  a1.set

lemma mem_a1_iff₀ {z : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ z ∈ᴮ a1 ↔ Γ ≤ z =ᴮ (0 : bSet 𝔹) ⊔ z =ᴮ (1 : bSet 𝔹) ⊔ z ∈ᴮ a1.aux := by
  rw [a1, a1.set, mem_insert1, mem_insert1]
  rw [sup_assoc]

lemma Ord_of_mem_a1 {Γ : 𝔹} {η : bSet 𝔹} (hMem : Γ ≤ η ∈ᴮ a1) :
    Γ ≤ Ord η :=
  a1.Ord_of_mem_set hMem

lemma eq_zero_iff_eq_empty {Γ : 𝔹} {u : bSet 𝔹} :
    Γ ≤ u =ᴮ (0 : bSet 𝔹) ↔ Γ ≤ u =ᴮ (∅ : bSet 𝔹) := by
  constructor
  · intro h
    exact bv_trans h ofNat_zero_eq_empty
  · intro h
    exact bv_trans h (bv_symm (ofNat_zero_eq_empty (Γ := Γ)))

/-- `a1.aux` contains every ordinal of size at most `omega`, except for the explicit `0` and `1`
cases handled by `a1` itself. -/
lemma mem_a1_of_injects_into_omega_aux {Γ : 𝔹} {η : bSet 𝔹}
    (hOrd : Γ ≤ Ord η) (hInj : Γ ≤ ⨆ f : bSet 𝔹, is_injective_function η omega f)
    (hNotZero : Γ ≤ (η =ᴮ (0 : bSet 𝔹))ᶜ)
    (hNotOne : Γ ≤ (η =ᴮ (1 : bSet 𝔹))ᶜ) :
    Γ ≤ η ∈ᴮ a1.aux := by
  apply (le_inf le_rfl hInj).trans
  apply lattice.bv_cases_right
  intro f
  let Δ : 𝔹 := Γ ⊓ is_injective_function η omega f
  change Δ ≤ η ∈ᴮ a1.aux
  let R : bSet 𝔹 := induced_epsilon_rel η omega f
  have hFunc : Δ ≤ is_function η omega f :=
    is_function_of_is_injective_function inf_le_right
  have hRmem : Δ ≤ R ∈ᴮ a1.candidates := by
    rw [a1.mem_candidates_iff]
    apply lattice.bv_use R
    apply le_inf
    · exact bv_powerset_spec.mp subset.mk_subset
    · apply le_inf bv_refl
      unfold a1.ϕ
      apply lattice.bv_use η
      apply le_inf
      · exact inf_le_left.trans hOrd
      · apply lattice.bv_use f
        apply le_inf
        · apply le_inf
          · exact inf_le_right
          · exact bv_refl
        · exact (nonempty_induced_rel_iff_not_zero_and_not_one
            (inf_le_left.trans hOrd) hFunc).mpr
            ⟨inf_le_left.trans hNotZero, inf_le_left.trans hNotOne⟩
  rw [a1.aux, mem_unfold]
  rw [mem_unfold] at hRmem
  apply (le_inf le_rfl hRmem).trans
  apply lattice.bv_cases_right
  intro χ
  let Θ : 𝔹 := Δ ⊓ (a1.candidateBVal χ ⊓ R =ᴮ a1.candidates.func χ)
  change Θ ≤ ⨆ i : a1.candidateType, a1.candidateBVal i ⊓ η =ᴮ a1.func i
  apply lattice.bv_use χ
  apply le_inf
  · dsimp [Θ, a1.candidateBVal]
    exact inf_le_right.trans inf_le_left
  · have hΘΔ : Θ ≤ Δ := by
      dsimp [Θ]
      exact inf_le_left
    have hχVal : Θ ≤ a1.candidates.bval χ := by
      dsimp [Θ, a1.candidateBVal]
      exact inf_le_right.trans inf_le_left
    have hREqχ : Θ ≤ R =ᴮ a1.candidates.func χ := by
      dsimp [Θ]
      exact inf_le_right.trans inf_le_right
    have hSpec : Θ ≤ a1.ψ (a1.candidates.func χ) (a1.func χ) :=
      a1.func_spec hχVal
    have hFuncOrd : Θ ≤ Ord (a1.func χ) :=
      hSpec.trans inf_le_left
    have hGsup : Θ ≤ ⨆ g : bSet 𝔹, is_injective_function (a1.func χ) omega g ⊓
        (induced_epsilon_rel (a1.func χ) omega g =ᴮ a1.candidates.func χ) ⊓
        (a1.candidates.func χ =ᴮ ∅)ᶜ :=
      hSpec.trans inf_le_right
    apply (le_inf le_rfl hGsup).trans
    apply lattice.bv_cases_right
    intro g
    let Ω : 𝔹 := Θ ⊓
      (is_injective_function (a1.func χ) omega g ⊓
        (induced_epsilon_rel (a1.func χ) omega g =ᴮ a1.candidates.func χ) ⊓
        (a1.candidates.func χ =ᴮ ∅)ᶜ)
    change Ω ≤ η =ᴮ a1.func χ
    have hΩΘ : Ω ≤ Θ := by
      dsimp [Ω]
      exact inf_le_left
    have hΩΔ : Ω ≤ Δ := hΩΘ.trans hΘΔ
    have hηOrd : Ω ≤ Ord η :=
      hΩΔ.trans (inf_le_left.trans hOrd)
    have hηInj : Ω ≤ is_injective_function η omega f :=
      hΩΔ.trans inf_le_right
    have hFuncOrdΩ : Ω ≤ Ord (a1.func χ) :=
      hΩΘ.trans hFuncOrd
    have hGInj : Ω ≤ is_injective_function (a1.func χ) omega g := by
      dsimp [Ω]
      exact inf_le_right.trans inf_le_left |>.trans inf_le_left
    have hGRel : Ω ≤ induced_epsilon_rel (a1.func χ) omega g =ᴮ a1.candidates.func χ := by
      dsimp [Ω]
      exact inf_le_right.trans inf_le_left |>.trans inf_le_right
    have hχNonempty : Ω ≤ (a1.candidates.func χ =ᴮ ∅)ᶜ := by
      dsimp [Ω]
      exact inf_le_right.trans inf_le_right
    have hRelEq : Ω ≤ induced_epsilon_rel η omega f =ᴮ
        induced_epsilon_rel (a1.func χ) omega g := by
      exact bv_trans (hΩΘ.trans hREqχ) (bv_symm hGRel)
    have hηExistsTwo : Ω ≤ exists_two η :=
      (exists_two_iff hηOrd).mpr (hΩΔ.trans (inf_le_left.trans hNotOne))
    have hFuncNonempty : Ω ≤
        (induced_epsilon_rel (a1.func χ) omega g =ᴮ ∅)ᶜ :=
      (le_inf (bv_symm hGRel) hχNonempty).trans
        ((B_ext_compl (B_ext_eq_left ∅)) (a1.candidates.func χ)
          (induced_epsilon_rel (a1.func χ) omega g))
    have hFuncNotOne : Ω ≤ (a1.func χ =ᴮ (1 : bSet 𝔹))ᶜ :=
      (nonempty_induced_rel_iff_not_zero_and_not_one
        hFuncOrdΩ (is_function_of_is_injective_function hGInj)).mp hFuncNonempty |>.2
    have hFuncExistsTwo : Ω ≤ exists_two (a1.func χ) :=
      (exists_two_iff hFuncOrdΩ).mpr hFuncNotOne
    exact eq_of_eq_induced_epsilon_rel hηOrd hFuncOrdΩ hηInj hGInj
      hRelEq hηExistsTwo hFuncExistsTwo

private theorem le_sup_of_inf_compl_le_local {a b c : 𝔹}
    (h : c ⊓ aᶜ ≤ b) : c ≤ a ⊔ b := by
  calc
    c = c ⊓ (a ⊔ aᶜ) := by rw [sup_compl_eq_top, inf_top_eq]
    _ = c ⊓ a ⊔ c ⊓ aᶜ := by rw [inf_sup_left]
    _ ≤ a ⊔ b := sup_le (inf_le_right.trans le_sup_left) (h.trans le_sup_right)

private theorem le_of_inf_compl_bot_local {a c : 𝔹}
    (h : c ⊓ aᶜ ≤ ⊥) : c ≤ a := by
  calc
    c = c ⊓ (a ⊔ aᶜ) := by rw [sup_compl_eq_top, inf_top_eq]
    _ = c ⊓ a ⊔ c ⊓ aᶜ := by rw [inf_sup_left]
    _ ≤ a := sup_le inf_le_right (h.trans bot_le)

lemma mem_a1_iff {Γ : 𝔹} {η : bSet 𝔹} (hOrd : Γ ≤ Ord η) :
    Γ ≤ η ∈ᴮ a1 ↔ Γ ≤ injects_into η omega := by
  constructor
  · intro hMem
    rw [mem_a1_iff₀] at hMem
    apply (le_inf le_rfl hMem).trans
    apply lattice.bv_or_elim_right
    · apply lattice.bv_or_elim_right
      · let Δ : 𝔹 := Γ ⊓ η =ᴮ (0 : bSet 𝔹)
        change Δ ≤ injects_into η omega
        have hEq : Δ ≤ η =ᴮ (0 : bSet 𝔹) := inf_le_right
        have hInjZero : Δ ≤ injects_into (0 : bSet 𝔹) omega :=
          injects_into_of_injection_into (injection_into_of_subset of_nat_subset_omega)
        exact (le_inf (bv_symm hEq) hInjZero).trans
          (B_ext_injects_into_left (y := omega) (0 : bSet 𝔹) η)
      · let Δ : 𝔹 := Γ ⊓ η =ᴮ (1 : bSet 𝔹)
        change Δ ≤ injects_into η omega
        have hEq : Δ ≤ η =ᴮ (1 : bSet 𝔹) := inf_le_right
        have hInjOne : Δ ≤ injects_into (1 : bSet 𝔹) omega :=
          injects_into_of_injection_into (injection_into_of_subset of_nat_subset_omega)
        exact (le_inf (bv_symm hEq) hInjOne).trans
          (B_ext_injects_into_left (y := omega) (1 : bSet 𝔹) η)
    · let Δ : 𝔹 := Γ ⊓ η ∈ᴮ a1.aux
      change Δ ≤ injects_into η omega
      have hAuxMem : Δ ≤ η ∈ᴮ a1.aux := inf_le_right
      rw [a1.aux, mem_unfold] at hAuxMem
      apply (le_inf le_rfl hAuxMem).trans
      apply lattice.bv_cases_right
      intro χ
      let Θ : 𝔹 := Δ ⊓ (a1.candidateBVal χ ⊓ η =ᴮ a1.func χ)
      change Θ ≤ injects_into η omega
      have hηEqFunc : Θ ≤ η =ᴮ a1.func χ := by
        dsimp [Θ]
        exact inf_le_right.trans inf_le_right
      have hχVal : Θ ≤ a1.candidates.bval χ := by
        dsimp [Θ, a1.candidateBVal]
        exact inf_le_right.trans inf_le_left
      have hSpec : Θ ≤ a1.ψ (a1.candidates.func χ) (a1.func χ) :=
        a1.func_spec hχVal
      have hGsup : Θ ≤ ⨆ g : bSet 𝔹, is_injective_function (a1.func χ) omega g ⊓
          (induced_epsilon_rel (a1.func χ) omega g =ᴮ a1.candidates.func χ) ⊓
          (a1.candidates.func χ =ᴮ ∅)ᶜ :=
        hSpec.trans inf_le_right
      apply (le_inf le_rfl hGsup).trans
      apply lattice.bv_cases_right
      intro g
      let Ω : 𝔹 := Θ ⊓
        (is_injective_function (a1.func χ) omega g ⊓
          (induced_epsilon_rel (a1.func χ) omega g =ᴮ a1.candidates.func χ) ⊓
          (a1.candidates.func χ =ᴮ ∅)ᶜ)
      change Ω ≤ injects_into η omega
      have hGInj : Ω ≤ is_injective_function (a1.func χ) omega g := by
        dsimp [Ω]
        exact inf_le_right.trans inf_le_left |>.trans inf_le_left
      have hFuncInjects : Ω ≤ injects_into (a1.func χ) omega :=
        injects_into_of_injection_into (by
          unfold injection_into
          apply lattice.bv_use g
          exact hGInj)
      exact (le_inf (bv_symm (inf_le_left.trans hηEqFunc)) hFuncInjects).trans
        (B_ext_injects_into_left (y := omega) (a1.func χ) η)
  · intro hInj
    rw [mem_a1_iff₀]
    apply le_sup_of_inf_compl_le_local
    let Θ : 𝔹 := Γ ⊓ (η =ᴮ (0 : bSet 𝔹) ⊔ η =ᴮ (1 : bSet 𝔹))ᶜ
    change Θ ≤ η ∈ᴮ a1.aux
    have hΘΓ : Θ ≤ Γ := by
      dsimp [Θ]
      exact inf_le_left
    have hΘOrd : Θ ≤ Ord η := hΘΓ.trans hOrd
    have hΘInj : Θ ≤ injection_into η omega :=
      injection_into_of_injects_into (hΘΓ.trans hInj)
    have hΘNotZero : Θ ≤ (η =ᴮ (0 : bSet 𝔹))ᶜ := by
      have hBoth : Θ ≤ (η =ᴮ (0 : bSet 𝔹))ᶜ ⊓ (η =ᴮ (1 : bSet 𝔹))ᶜ := by
        simpa [Θ, compl_sup] using
          (inf_le_right : Θ ≤ (η =ᴮ (0 : bSet 𝔹) ⊔ η =ᴮ (1 : bSet 𝔹))ᶜ)
      exact hBoth.trans inf_le_left
    have hΘNotOne : Θ ≤ (η =ᴮ (1 : bSet 𝔹))ᶜ := by
      have hBoth : Θ ≤ (η =ᴮ (0 : bSet 𝔹))ᶜ ⊓ (η =ᴮ (1 : bSet 𝔹))ᶜ := by
        simpa [Θ, compl_sup] using
          (inf_le_right : Θ ≤ (η =ᴮ (0 : bSet 𝔹) ⊔ η =ᴮ (1 : bSet 𝔹))ᶜ)
      exact hBoth.trans inf_le_right
    exact mem_a1_of_injects_into_omega_aux hΘOrd hΘInj hΘNotZero hΘNotOne

lemma a1_transitive {Γ : 𝔹} : Γ ≤ is_transitive a1 := by
  unfold is_transitive
  apply le_iInf
  intro z
  apply lattice.bv_imp_intro
  let Δ : 𝔹 := Γ ⊓ z ∈ᴮ a1
  change Δ ≤ z ⊆ᴮ a1
  rw [subset_unfold']
  apply le_iInf
  intro w
  apply lattice.bv_imp_intro
  let Θ : 𝔹 := Δ ⊓ w ∈ᴮ z
  change Θ ≤ w ∈ᴮ a1
  have hzMem : Θ ≤ z ∈ᴮ a1 := by
    dsimp [Θ, Δ]
    exact inf_le_left.trans inf_le_right
  have hwMemZ : Θ ≤ w ∈ᴮ z := by
    dsimp [Θ]
    exact inf_le_right
  have hzOrd : Θ ≤ Ord z :=
    Ord_of_mem_a1 hzMem
  have hwOrd : Θ ≤ Ord w :=
    Ord_of_mem_Ord hwMemZ hzOrd
  rw [mem_a1_iff hwOrd]
  have hzInj : Θ ≤ injects_into z omega :=
    (mem_a1_iff hzOrd).mp hzMem
  have hzInj' : Θ ≤ injection_into z omega :=
    injection_into_of_injects_into hzInj
  apply (le_inf le_rfl hzInj').trans
  apply lattice.bv_cases_right
  intro f
  let Ω : 𝔹 := Θ ⊓ is_injective_function z omega f
  change Ω ≤ injects_into w omega
  have hwSubZ : Ω ≤ w ⊆ᴮ z :=
    subset_of_mem_transitive (inf_le_left.trans hzOrd |>.trans inf_le_right)
      (inf_le_left.trans hwMemZ)
  have hwInjZ : Ω ≤ injection_into w z :=
    injection_into_of_subset hwSubZ
  apply (le_inf le_rfl hwInjZ).trans
  apply lattice.bv_cases_right
  intro g
  let Ξ : 𝔹 := Ω ⊓ is_injective_function w z g
  change Ξ ≤ injects_into w omega
  apply injects_into_of_injection_into
  unfold injection_into
  apply lattice.bv_use (injective_function_comp inf_le_right (inf_le_left.trans inf_le_right))
  exact injective_function_comp_is_injective_function

lemma a1_ewo {Γ : 𝔹} : Γ ≤ epsilon_well_orders a1 := by
  refine le_inf ?_ ?_
  · apply epsilon_trichotomy_of_sub_Ord
    apply le_iInf
    intro x
    apply lattice.bv_imp_intro
    exact Ord_of_mem_a1 inf_le_right
  · exact epsilon_wf_of_sub_Ord a1

lemma a1_Ord {Γ : 𝔹} : Γ ≤ Ord a1 :=
  le_inf a1_ewo a1_transitive

lemma a1_not_le_omega {Γ : 𝔹} : Γ ≤ (injects_into a1 omega)ᶜ := by
  rw [le_compl_iff_disjoint_right, disjoint_iff]
  apply le_antisymm ?_ bot_le
  let Δ : 𝔹 := Γ ⊓ injects_into a1 omega
  change Δ ≤ ⊥
  have hMemSelf : Δ ≤ a1 ∈ᴮ a1 :=
    (mem_a1_iff a1_Ord).mpr inf_le_right
  exact bot_of_mem_self hMemSelf

lemma a1_spec {Γ : 𝔹} : Γ ≤ aleph_one_Ord_spec a1 := by
  unfold aleph_one_Ord_spec
  apply le_inf
  · exact a1_not_le_omega
  · apply le_inf
    · exact a1_Ord
    · apply le_iInf
      intro η
      apply lattice.bv_imp_intro
      apply lattice.bv_imp_intro
      let Δ : 𝔹 := (Γ ⊓ Ord η) ⊓ (injects_into η omega)ᶜ
      change Δ ≤ a1 ⊆ᴮ η
      have hΔΓ : Δ ≤ Γ := by
        dsimp [Δ]
        exact inf_le_left.trans inf_le_left
      have hηOrd : Δ ≤ Ord η := by
        dsimp [Δ]
        exact inf_le_left.trans inf_le_right
      have hηNoInj : Δ ≤ (injects_into η omega)ᶜ := by
        dsimp [Δ]
        exact inf_le_right
      rw [Ord.le_iff_lt_or_eq (hΔΓ.trans a1_Ord) hηOrd]
      have hTri : Δ ≤ a1 =ᴮ η ⊔ a1 ∈ᴮ η ⊔ η ∈ᴮ a1 :=
        Ord.trichotomy (hΔΓ.trans a1_Ord) hηOrd
      apply (le_inf le_rfl hTri).trans
      apply lattice.bv_or_elim_right
      · apply lattice.bv_or_elim_right
        · exact inf_le_right.trans
            (le_sup_right : a1 =ᴮ η ≤ a1 ∈ᴮ η ⊔ a1 =ᴮ η)
        · exact inf_le_right.trans
            (le_sup_left : a1 ∈ᴮ η ≤ a1 ∈ᴮ η ⊔ a1 =ᴮ η)
      · let Θ : 𝔹 := Δ ⊓ η ∈ᴮ a1
        change Θ ≤ a1 ∈ᴮ η ⊔ a1 =ᴮ η
        have hηMemA1 : Θ ≤ η ∈ᴮ a1 := inf_le_right
        have hηInj : Θ ≤ injects_into η omega :=
          (mem_a1_iff (inf_le_left.trans hηOrd)).mp hηMemA1
        have hηNoInjΘ : Θ ≤ (injects_into η omega)ᶜ :=
          inf_le_left.trans hηNoInj
        exact lattice.bv_exfalso ((le_inf hηInj hηNoInjΘ).trans (by simp))

lemma larger_than_of_not_exists_mem {x y : bSet 𝔹} {Γ : 𝔹}
    (hEmpty : Γ ≤ (exists_mem y)ᶜ) : Γ ≤ larger_than x y := by
  unfold larger_than
  have hisSurj : Γ ≤ is_surj (∅ : bSet 𝔹) y (∅ : bSet 𝔹) := by
    unfold is_surj
    apply le_iInf
    intro v
    apply lattice.bv_imp_intro
    let Δ : 𝔹 := Γ ⊓ v ∈ᴮ y
    change Δ ≤ ⨆ w : bSet 𝔹, w ∈ᴮ (∅ : bSet 𝔹) ⊓ pair w v ∈ᴮ (∅ : bSet 𝔹)
    have hMemLe : v ∈ᴮ y ≤ exists_mem y :=
      le_iSup (fun z : bSet 𝔹 => z ∈ᴮ y) v
    have hBot : Δ ≤ ⊥ := by
      calc
        Δ ≤ (exists_mem y)ᶜ ⊓ exists_mem y :=
          le_inf (inf_le_left.trans hEmpty) (inf_le_right.trans hMemLe)
        _ = ⊥ := by simp
    exact hBot.trans bot_le
  apply lattice.bv_use (∅ : bSet 𝔹)
  apply lattice.bv_use (∅ : bSet 𝔹)
  exact le_inf (le_inf empty_subset is_func'_empty) hisSurj

lemma not_injects_into_omega_of_not_larger_omega {x : bSet 𝔹} {Γ : 𝔹}
    (hNotLarger : Γ ≤ (larger_than omega x)ᶜ) :
    Γ ≤ (injects_into x omega)ᶜ := by
  rw [le_compl_iff_disjoint_right, disjoint_iff]
  apply le_antisymm ?_ bot_le
  let Δ : 𝔹 := Γ ⊓ injects_into x omega
  change Δ ≤ ⊥
  have hSplit : Δ = (Δ ⊓ exists_mem x) ⊔ (Δ ⊓ (exists_mem x)ᶜ) := by
    calc
      Δ = Δ ⊓ ⊤ := by simp
      _ = Δ ⊓ (exists_mem x ⊔ (exists_mem x)ᶜ) := by simp
      _ = (Δ ⊓ exists_mem x) ⊔ (Δ ⊓ (exists_mem x)ᶜ) := by rw [inf_sup_left]
  rw [hSplit]
  apply sup_le
  · let Λ : 𝔹 := Δ ⊓ exists_mem x
    change Λ ≤ ⊥
    have hΛInj : Λ ≤ injects_into x omega := by
      dsimp [Λ, Δ]
      exact inf_le_left.trans inf_le_right
    have hΛExists : Λ ≤ exists_mem x := inf_le_right
    have hSurj : Λ ≤ surjects_onto omega x :=
      surjects_onto_of_injects_into hΛInj hΛExists
    have hLarger : Λ ≤ larger_than omega x :=
      larger_than_of_surjects_onto hSurj
    have hNot : Λ ≤ (larger_than omega x)ᶜ := by
      dsimp [Λ, Δ]
      exact inf_le_left.trans (inf_le_left.trans hNotLarger)
    exact (le_inf hLarger hNot).trans (by simp)
  · let Λ : 𝔹 := Δ ⊓ (exists_mem x)ᶜ
    change Λ ≤ ⊥
    have hLarger : Λ ≤ larger_than omega x :=
      larger_than_of_not_exists_mem inf_le_right
    have hNot : Λ ≤ (larger_than omega x)ᶜ := by
      dsimp [Λ, Δ]
      exact inf_le_left.trans (inf_le_left.trans hNotLarger)
    exact (le_inf hLarger hNot).trans (by simp)

lemma a1_le_of_omega_lt {Γ : 𝔹} : Γ ≤ le_of_omega_lt a1 := by
  unfold le_of_omega_lt
  apply le_iInf
  intro x
  apply lattice.bv_imp_intro
  apply lattice.bv_imp_intro
  let Δ : 𝔹 := (Γ ⊓ Ord x) ⊓ (larger_than omega x)ᶜ
  change Δ ≤ injects_into a1 x
  have hΔΓ : Δ ≤ Γ := by
    dsimp [Δ]
    exact inf_le_left.trans inf_le_left
  have hxOrd : Δ ≤ Ord x := by
    dsimp [Δ]
    exact inf_le_left.trans inf_le_right
  have hNotLarger : Δ ≤ (larger_than omega x)ᶜ := by
    dsimp [Δ]
    exact inf_le_right
  have hxNoInj : Δ ≤ (injects_into x omega)ᶜ :=
    not_injects_into_omega_of_not_larger_omega hNotLarger
  have hxNotMemA1 : Δ ≤ (x ∈ᴮ a1)ᶜ := by
    rw [le_compl_iff_disjoint_right, disjoint_iff]
    apply le_antisymm ?_ bot_le
    let Θ : 𝔹 := Δ ⊓ x ∈ᴮ a1
    change Θ ≤ ⊥
    have hxMem : Θ ≤ x ∈ᴮ a1 := inf_le_right
    have hxInj : Θ ≤ injects_into x omega :=
      (mem_a1_iff (inf_le_left.trans hxOrd)).mp hxMem
    have hxNoInjΘ : Θ ≤ (injects_into x omega)ᶜ :=
      inf_le_left.trans hxNoInj
    exact (le_inf hxInj hxNoInjΘ).trans (by simp)
  apply injects_into_of_subset
  rw [Ord.le_iff_lt_or_eq (hΔΓ.trans a1_Ord) hxOrd]
  have hTri : Δ ≤ a1 =ᴮ x ⊔ a1 ∈ᴮ x ⊔ x ∈ᴮ a1 :=
    Ord.trichotomy (hΔΓ.trans a1_Ord) hxOrd
  apply (le_inf le_rfl hTri).trans
  apply lattice.bv_or_elim_right
  · apply lattice.bv_or_elim_right
    · exact inf_le_right.trans
        (le_sup_right : a1 =ᴮ x ≤ a1 ∈ᴮ x ⊔ a1 =ᴮ x)
    · exact inf_le_right.trans
        (le_sup_left : a1 ∈ᴮ x ≤ a1 ∈ᴮ x ⊔ a1 =ᴮ x)
  · let Θ : 𝔹 := Δ ⊓ x ∈ᴮ a1
    change Θ ≤ a1 ∈ᴮ x ⊔ a1 =ᴮ x
    have hxMem : Θ ≤ x ∈ᴮ a1 := inf_le_right
    have hxNotMem : Θ ≤ (x ∈ᴮ a1)ᶜ :=
      inf_le_left.trans hxNotMemA1
    exact lattice.bv_exfalso ((le_inf hxMem hxNotMem).trans (by simp))

lemma injects_into_omega_of_mem_aleph_one_check {Γ : 𝔹} {z : bSet 𝔹}
    (hMem : Γ ≤ z ∈ᴮ (check pSet.aleph_one : bSet 𝔹)) :
    Γ ≤ injects_into z omega := by
  rw [mem_unfold] at hMem
  apply (le_inf le_rfl hMem).trans
  apply lattice.bv_cases_right
  intro η
  let Δ : 𝔹 := Γ ⊓
    ((check pSet.aleph_one : bSet 𝔹).bval η ⊓
      z =ᴮ (check pSet.aleph_one : bSet 𝔹).func η)
  change Δ ≤ injects_into z omega
  have hzEq : Δ ≤ z =ᴮ (check pSet.aleph_one : bSet 𝔹).func η := by
    dsimp [Δ]
    exact inf_le_right.trans inf_le_right
  have hInjCheck : Δ ≤ injects_into ((check pSet.aleph_one : bSet 𝔹).func η) omega := by
    rw [check_func]
    exact check_injects_into (pSet.injects_into_omega_of_mem_aleph_one (by simp))
  exact (le_inf (bv_symm hzEq) hInjCheck).trans
    (B_ext_injects_into_left (y := omega) ((check pSet.aleph_one : bSet 𝔹).func η) z)

lemma mem_aleph_one_of_injects_into_omega {x z : bSet 𝔹} {Γ : 𝔹}
    (hAlephOne : Γ ≤ aleph_one_Ord_spec x)
    (hXOrd : Γ ≤ Ord x) (hZOrd : Γ ≤ Ord z)
    (hZInj : Γ ≤ injects_into z omega) :
    Γ ≤ z ∈ᴮ x := by
  apply le_of_inf_compl_bot_local
  let Δ : 𝔹 := Γ ⊓ (z ∈ᴮ x)ᶜ
  change Δ ≤ ⊥
  have hΔΓ : Δ ≤ Γ := inf_le_left
  have hNotMem : Δ ≤ (z ∈ᴮ x)ᶜ := inf_le_right
  have hLe : Δ ≤ x ⊆ᴮ z := by
    rw [Ord.le_iff_lt_or_eq (hΔΓ.trans hXOrd) (hΔΓ.trans hZOrd)]
    exact Ord.resolve_lt (hΔΓ.trans hZOrd) (hΔΓ.trans hXOrd) hNotMem
  have hXInj : Δ ≤ injects_into x omega :=
    injects_into_trans (injects_into_of_subset hLe) (hΔΓ.trans hZInj)
  have hNoXInj : Δ ≤ (injects_into x omega)ᶜ :=
    hΔΓ.trans (hAlephOne.trans inf_le_left)
  exact (le_inf hXInj hNoXInj).trans (by simp)

lemma aleph_one_check_sub_aleph_one_aux {x : bSet 𝔹} {Γ : 𝔹}
    (hOrd : Γ ≤ Ord x) (hAlephOne : Γ ≤ aleph_one_Ord_spec x) :
    Γ ≤ (check pSet.aleph_one : bSet 𝔹) ⊆ᴮ x := by
  rw [subset_unfold']
  apply le_iInf
  intro w
  apply lattice.bv_imp_intro
  let Δ : 𝔹 := Γ ⊓ w ∈ᴮ (check pSet.aleph_one : bSet 𝔹)
  change Δ ≤ w ∈ᴮ x
  exact mem_aleph_one_of_injects_into_omega
    (inf_le_left.trans hAlephOne)
    (inf_le_left.trans hOrd)
    (Ord_of_mem_Ord inf_le_right (check_Ord pSet.aleph_one_Ord))
    (injects_into_omega_of_mem_aleph_one_check inf_le_right)

end bSet

end Flypitch
