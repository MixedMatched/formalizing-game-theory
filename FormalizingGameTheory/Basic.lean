import Mathlib.Tactic
import Aesop

-- a Utility is a Rational number representing the payoff for a single player of a given set of strategies
-- (should probably eventually be something with total order and optional decidability)

-- a PureStrategy is an instance of the strategy type
@[aesop safe [constructors, cases]]
structure PureStrategy (A : Type) := (val : A)

def PureStrategy.cast : PureStrategy A → A = M → PureStrategy M := by
  intro PS_A A_eq_M
  subst A_eq_M
  exact PS_A

-- a MixedStrategy is a probability distribution over PureStrategies
@[aesop safe [constructors, cases]]
structure MixedStrategy (A : Type) :=
  (strategies: List (PureStrategy A))
  (probabilities: List Rat)
  (probabilities_sum_to_one: List.foldl Rat.add 0 probabilities = 1)
  (probabilities_non_negative: List.all probabilities (λ p => p > 0))
  (same_length: List.length strategies = List.length probabilities)

def PureStrategy.asMixed : PureStrategy A → MixedStrategy A :=
  λ ps =>
    {
      strategies := [ps]
      probabilities := [1]
      probabilities_sum_to_one := by
        simp_all only [List.foldl_cons, List.foldl_nil, Rat.add, Rat.den_ofNat, Nat.gcd_self, ↓reduceDIte, Rat.num_ofNat, Nat.cast_one,
          mul_one, zero_add, Rat.mk_den_one, Int.cast_one]
      probabilities_non_negative := by simp_all only [gt_iff_lt, List.all_cons, zero_lt_one, decide_True, List.all_nil, Bool.and_self]
      same_length := by simp_all only [List.length_singleton]
    }

def MixedStrategy.isPure : MixedStrategy A → Prop :=
  λ m => m.strategies.length = 1

def MixedStrategy.asPure : (m: MixedStrategy A) → m.isPure → PureStrategy A :=
  λ m pure => m.strategies[0]'(by exact Nat.lt_of_sub_eq_succ pure)

def MixedStrategy.length_not_zero : (m: MixedStrategy A) → m.strategies.length ≠ 0 := by
  intro m
  simp_all only [ne_eq, List.length_eq_zero]
  apply Aesop.BuiltinRules.not_intro
  intro a
  obtain ⟨strategies, probabilities, probabilities_sum_to_one, probabilities_non_negative, same_length⟩ := m
  subst a
  simp_all only [gt_iff_lt, List.all_eq_true, decide_eq_true_eq, List.length_nil]
  cases probabilities
  . unfold List.foldl at probabilities_sum_to_one
    trivial
  . simp_all only [List.foldl_cons, List.mem_cons, forall_eq_or_imp, List.length_cons, self_eq_add_left,
    AddLeftCancelMonoid.add_eq_zero, List.length_eq_zero, one_ne_zero, and_false]

-- a PureStrategyProfile is a list of PureStrategy (for type reasons, we need to use a function)
@[aesop safe [constructors, cases]]
structure PureStrategyProfile (L: List Type) where
  (strategies: (i: Fin (List.length L)) → PureStrategy (List.get L i))

-- a MixedStrategyProfile is a list of MixedStrategy (for type reasons, we need to use a function)
@[aesop safe [constructors, cases]]
structure MixedStrategyProfile (L: List Type) where
  (strategies: (i: Fin (List.length L)) → MixedStrategy (List.get L i))

def MixedStrategyProfile.isPure : MixedStrategyProfile L → Prop :=
  λ msp => ∀ (i: Fin (List.length L)), (msp.strategies i).isPure

def MixedStrategyProfile.asPure : (msp: MixedStrategyProfile L) → msp.isPure → PureStrategyProfile L :=
  λ msp pure => ⟨λ i => (msp.strategies i).asPure (pure i)⟩

-- a UtilityProfile is a list of utilities
@[aesop safe [constructors, cases]]
structure UtilityProfile (L: List Type) where
  (utilities: List Rat)
  (same_length: L.length = utilities.length)
deriving BEq, DecidableEq

def UtilityProfile.cast : UtilityProfile A → A.length = B.length → UtilityProfile B := by
  intro upa a_eq_b
  exact ⟨upa.utilities, by obtain ⟨utilities, same_length⟩ := upa; simp_all only⟩

theorem Fin_can_index_utilities (i: Fin L.length) (up: UtilityProfile L) : ↑i < up.utilities.length := by
  obtain ⟨utilities, same_length⟩ := up
  simp_all only
  let i_isLt := i.isLt
  simp only [same_length] at i_isLt
  exact i_isLt

theorem Nat_can_index_utilities (i: Nat) (up: UtilityProfile L) (i_isLt: i < L.length) : i < up.utilities.length := by
  obtain ⟨utilities, same_length⟩ := up
  simp_all only

@[aesop safe unfold]
instance UtilityProfile.add : Add (UtilityProfile L) where
  add x y := by
    let utilities : List Rat := List.zipWith
      Rat.add
      x.utilities
      y.utilities
    let same_length : L.length = utilities.length := by
      unfold utilities
      simp_all only [List.length_zipWith]
      obtain ⟨utilities_1, same_length_1⟩ := x
      obtain ⟨utilities_2, same_length_2⟩ := y
      simp_all only
      rw [← same_length_1, ← same_length_2]
      simp_all only [min_self]
    let up : UtilityProfile L := ⟨utilities, same_length⟩
    exact up

theorem UtilityProfile.length_add_left (a b c : UtilityProfile L) : a + b = c → a.utilities.length = c.utilities.length := by
  intro a_1
  subst a_1
  unfold UtilityProfile.add HAdd.hAdd instHAdd Add.add
  simp_all only [List.length_zipWith]
  obtain ⟨utilities, same_length⟩ := a
  obtain ⟨utilities_1, same_length_1⟩ := b
  simp_all only
  simp_all only [min_self]

theorem UtilityProfile.length_add_right (a b c : UtilityProfile L) : a + b = c → b.utilities.length = c.utilities.length := by
  intro a_1
  subst a_1
  unfold UtilityProfile.add HAdd.hAdd instHAdd Add.add
  simp_all only [List.length_zipWith]
  obtain ⟨utilities, same_length⟩ := a
  obtain ⟨utilities_1, same_length_1⟩ := b
  simp_all only
  simp_all only [min_self]

theorem list_zipWith_left_intro (a b c : List ℚ)
    (a_len : a.length = c.length) (b_len : b.length = c.length)
    (cacb : List.zipWith (· + ·) c a = List.zipWith (· + ·) c b) :
    a = b := by
  induction c generalizing a b with
  | nil =>
    revert a_len b_len
    simp_all only [List.zipWith_nil_left, List.length_nil, List.length_eq_zero, implies_true]
  | cons c cs ih =>
      match a, b with
      | [], _ => simp at a_len
      | _, [] => simp at b_len
      | a::as, b::bs =>
        simp only [List.length_cons, add_left_inj] at a_len b_len
        simp only [List.zipWith_cons_cons, List.cons.injEq, add_right_inj] at cacb
        specialize ih _ _ a_len b_len cacb.2
        simp [cacb.1, ih]

theorem UtilityProfile.add_left_intro (a b c : UtilityProfile L) (cacb: c + a = c + b) : a = b := by
  unfold UtilityProfile.add HAdd.hAdd instHAdd Add.add at cacb
  simp_all only [mk.injEq]
  obtain ⟨utilities_1, same_length_1⟩ := a
  obtain ⟨utilities_2, same_length_2⟩ := b
  obtain ⟨utilities, same_length⟩ := c
  simp_all only [mk.injEq]
  simp_all only
  symm at same_length_2
  rw [same_length_2] at same_length_1
  exact list_zipWith_left_intro utilities_1 utilities_2 utilities same_length_2 same_length_1 cacb

theorem index_list_zipWith_left_intro (a b c : List ℚ) (i: Fin c.length)
    (a_len : a.length = c.length) (b_len : b.length = c.length)
    (cacb :
      (List.zipWith (· + ·) c a)[i]'(by simp_all only [Fin.is_lt, List.length_zipWith, min_self])
      = (List.zipWith (· + ·) c b)[i]'(by simp_all only [Fin.is_lt, List.length_zipWith, min_self])
    ):
    a[i] = b[i] := by
  induction c generalizing a b with
  | nil =>
    revert a_len b_len
    simp_all only [List.zipWith_nil_left, List.length_nil, List.length_eq_zero, implies_true]
  | cons c cs _ =>
    match a, b with
    | [], _ => simp at a_len
    | _, [] => simp at b_len
    | a::as, b::bs =>
      simp only [List.length_cons, add_left_inj] at a_len b_len
      simp only [List.zipWith_cons_cons, List.cons.injEq, add_right_inj] at cacb
      cases i
      case mk val isLt =>
        induction val
        case zero =>
          simp_all only [Fin.is_lt, Fin.getElem_fin, List.getElem_zipWith, add_right_inj, implies_true, imp_self,
            lt_add_iff_pos_left, add_pos_iff, zero_lt_one, or_true, List.length_cons, Fin.zero_eta, Fin.val_zero,
            List.getElem_cons_zero]
        case succ n _ =>
          simp_all only [Fin.getElem_fin, List.getElem_zipWith, add_right_inj, implies_true,
            List.length_cons, List.getElem_cons_succ]

theorem UtilityProfile.index_add_left_intro (a b c : UtilityProfile L) (i: Fin L.length)
    (cacb:
      (c + a).utilities[i]'(by exact Fin_can_index_utilities i (c + a))
      = (c + b).utilities[i]'(by exact Fin_can_index_utilities i (c + b))):
    a.utilities[i]'(by exact Fin_can_index_utilities i a)
      = b.utilities[i]'(by exact Fin_can_index_utilities i b) := by
  unfold UtilityProfile.add HAdd.hAdd instHAdd Add.add at cacb
  obtain ⟨utilities_1, same_length_1⟩ := a
  obtain ⟨utilities_2, same_length_2⟩ := b
  obtain ⟨utilities, same_length⟩ := c
  simp_all only
  rw [same_length] at same_length_1 same_length_2
  symm at same_length_1 same_length_2
  exact index_list_zipWith_left_intro utilities_1 utilities_2 utilities (i.cast same_length) same_length_1 same_length_2 cacb

theorem index_lt_list_zipWith_left_intro (a b c : List ℚ) (i: Fin c.length)
    (a_len : a.length = c.length) (b_len : b.length = c.length)
    (cacb :
      (List.zipWith (· + ·) c a)[i]'(by simp_all only [Fin.is_lt, List.length_zipWith, min_self])
      < (List.zipWith (· + ·) c b)[i]'(by simp_all only [Fin.is_lt, List.length_zipWith, min_self])
    ):
    a[i] < b[i] := by
  induction c generalizing a b with
  | nil =>
    revert a_len b_len
    simp_all only [List.zipWith_nil_left, List.length_nil, List.length_eq_zero, implies_true]
  | cons c cs _ =>
    match a, b with
    | [], _ => simp at a_len
    | _, [] => simp at b_len
    | a::as, b::bs =>
      simp only [List.length_cons, add_left_inj] at a_len b_len
      simp only [List.zipWith_cons_cons, List.cons.injEq, add_right_inj] at cacb
      cases i
      case mk val isLt =>
        induction val
        case zero =>
          simp_all only [Fin.getElem_fin, List.getElem_zipWith, add_lt_add_iff_left, implies_true,
            List.length_cons, Fin.zero_eta, Fin.val_zero, List.getElem_cons_zero]
        case succ n _ =>
          simp_all only [Fin.getElem_fin, List.getElem_zipWith, add_lt_add_iff_left, implies_true,
            List.length_cons, gt_iff_lt, List.getElem_cons_succ]

theorem UtilityProfile.index_lt_add_left_intro (a b c : UtilityProfile L) (i: Fin L.length)
    (cacb:
      (c + a).utilities[i]'(by exact Fin_can_index_utilities i (c + a))
        < (c + b).utilities[i]'(by exact Fin_can_index_utilities i (c + b))):
    a.utilities[i]'(by exact Fin_can_index_utilities i a)
      < b.utilities[i]'(by exact Fin_can_index_utilities i b) := by
  unfold UtilityProfile.add HAdd.hAdd instHAdd Add.add at cacb
  obtain ⟨utilities_1, same_length_1⟩ := a
  obtain ⟨utilities_2, same_length_2⟩ := b
  obtain ⟨utilities, same_length⟩ := c
  simp_all only
  rw [same_length] at same_length_1 same_length_2
  symm at same_length_1 same_length_2
  exact index_lt_list_zipWith_left_intro utilities_1 utilities_2 utilities (i.cast same_length) same_length_1 same_length_2 cacb

theorem UtilityProfile.index_nat_lt_add_left_intro (a b c : UtilityProfile L) (i: Nat) (i_Lt: i < L.length)
    (cacb:
      (c + a).utilities[i]'(by exact Nat_can_index_utilities i (c + a) i_Lt)
        < (c + b).utilities[i]'(by exact Nat_can_index_utilities i (c + b) i_Lt)):
    a.utilities[i]'(by exact Nat_can_index_utilities i a i_Lt)
      < b.utilities[i]'(by exact Nat_can_index_utilities i b i_Lt) := by
  unfold UtilityProfile.add HAdd.hAdd instHAdd Add.add at cacb
  obtain ⟨utilities_1, same_length_1⟩ := a
  obtain ⟨utilities_2, same_length_2⟩ := b
  obtain ⟨utilities, same_length⟩ := c
  simp_all only
  rw [same_length] at same_length_1 same_length_2 i_Lt
  symm at same_length_1 same_length_2
  exact index_lt_list_zipWith_left_intro utilities_1 utilities_2 utilities ⟨i, i_Lt⟩ same_length_1 same_length_2 cacb

theorem list_zipWith_left_cancel (a b c : List ℚ)
    (a_len : a.length = c.length) (b_len : b.length = c.length)
    (a_eq_b : a = b) :
    List.zipWith (· + ·) c a = List.zipWith (· + ·) c b := by
  induction c generalizing a b with
  | nil =>
    revert a_len b_len
    simp_all only [List.zipWith_nil_left, List.length_nil, List.length_eq_zero, implies_true]
  | cons c cs ih =>
      match a, b with
      | [], _ => simp at a_len
      | _, [] => simp at b_len
      | a::as, b::bs =>
        simp only [List.length_cons, add_left_inj] at a_len b_len
        simp only [List.zipWith_cons_cons, List.cons.injEq, add_right_inj] at a_eq_b
        specialize ih _ _ a_len b_len a_eq_b.2
        simp [a_eq_b.1, ih]

theorem UtilityProfile.add_left_cancel (a b c : UtilityProfile L) (a_eq_b: a = b) : c + a = c + b := by
  subst a_eq_b
  unfold UtilityProfile.add
  simp_all only

theorem index_list_zipWith_left_cancel (a b c : List ℚ) (i: Fin c.length)
    (a_len : a.length = c.length) (b_len : b.length = c.length)
    (a_eq_b : a[i] = b[i]):
    (List.zipWith (· + ·) c a)[i]'(by simp_all only [Fin.is_lt, List.length_zipWith, min_self])
      = (List.zipWith (· + ·) c b)[i]'(by simp_all only [Fin.is_lt, List.length_zipWith, min_self])
    := by
  induction c generalizing a b with
  | nil =>
    revert a_len b_len
    simp_all only [List.zipWith_nil_left, List.length_nil, List.length_eq_zero, implies_true]
  | cons c cs _ =>
    match a, b with
    | [], _ => simp at a_len
    | _, [] => simp at b_len
    | a::as, b::bs =>
      simp only [List.length_cons, add_left_inj] at a_len b_len
      simp only [List.zipWith_cons_cons, List.cons.injEq, add_right_inj]
      cases i
      case mk val isLt =>
        induction val
        case zero =>
          simp_all only [Fin.is_lt, Fin.getElem_fin, List.getElem_zipWith, add_right_inj, implies_true, imp_self,
            lt_add_iff_pos_left, add_pos_iff, zero_lt_one, or_true, List.length_cons, Fin.zero_eta, Fin.val_zero,
            List.getElem_cons_zero]
        case succ n _ =>
          simp_all only [Fin.getElem_fin, List.getElem_zipWith, add_right_inj, implies_true,
            List.length_cons, List.getElem_cons_succ]

theorem UtilityProfile.index_add_left_cancel (a b c : UtilityProfile L) (i: Fin L.length)
    (a_eq_b:
      a.utilities[i]'(by exact Fin_can_index_utilities i a)
        = b.utilities[i]'(by exact Fin_can_index_utilities i b)
    ):
    (c + a).utilities[i]'(by exact Fin_can_index_utilities i (c + a))
      = (c + b).utilities[i]'(by exact Fin_can_index_utilities i (c + b)) := by
  unfold UtilityProfile.add HAdd.hAdd instHAdd Add.add
  obtain ⟨utilities_1, same_length_1⟩ := a
  obtain ⟨utilities_2, same_length_2⟩ := b
  obtain ⟨utilities, same_length⟩ := c
  simp_all only
  rw [same_length] at same_length_1 same_length_2
  symm at same_length_1 same_length_2
  exact index_list_zipWith_left_cancel utilities_1 utilities_2 utilities (i.cast same_length) same_length_1 same_length_2 a_eq_b

theorem index_lt_list_zipWith_left_cancel (a b c : List ℚ) (i: Fin c.length)
    (a_len : a.length = c.length) (b_len : b.length = c.length)
    (a_lt_b : a[i] < b[i]):
    (List.zipWith (· + ·) c a)[i]'(by simp_all only [Fin.is_lt, List.length_zipWith, min_self])
      < (List.zipWith (· + ·) c b)[i]'(by simp_all only [Fin.is_lt, List.length_zipWith, min_self]) := by
  induction c generalizing a b with
  | nil =>
    revert a_len b_len
    simp_all only [List.zipWith_nil_left, List.length_nil, List.length_eq_zero, implies_true]
  | cons c cs _ =>
    match a, b with
    | [], _ => simp at a_len
    | _, [] => simp at b_len
    | a::as, b::bs =>
      simp only [List.length_cons, add_left_inj] at a_len b_len
      simp only [List.zipWith_cons_cons, List.cons.injEq, add_right_inj]
      cases i
      case mk val isLt =>
        induction val
        case zero =>
          simp_all only [Fin.getElem_fin, List.getElem_zipWith, add_lt_add_iff_left, implies_true,
            List.length_cons, Fin.zero_eta, Fin.val_zero, List.getElem_cons_zero]
        case succ n _ =>
          simp_all only [Fin.getElem_fin, List.getElem_zipWith, add_lt_add_iff_left, implies_true,
            List.length_cons, gt_iff_lt, List.getElem_cons_succ]

theorem UtilityProfile.index_lt_add_left_cancel (a b c : UtilityProfile L) (i: Fin L.length)
    (a_lt_b:
      a.utilities[i]'(by exact Fin_can_index_utilities i a)
        < b.utilities[i]'(by exact Fin_can_index_utilities i b)
    ):
    (c + a).utilities[i]'(by exact Fin_can_index_utilities i (c + a))
        < (c + b).utilities[i]'(by exact Fin_can_index_utilities i (c + b)):= by
  unfold UtilityProfile.add HAdd.hAdd instHAdd Add.add
  obtain ⟨utilities_1, same_length_1⟩ := a
  obtain ⟨utilities_2, same_length_2⟩ := b
  obtain ⟨utilities, same_length⟩ := c
  simp_all only
  rw [same_length] at same_length_1 same_length_2
  symm at same_length_1 same_length_2
  exact index_lt_list_zipWith_left_cancel utilities_1 utilities_2 utilities (i.cast same_length) same_length_1 same_length_2 a_lt_b

theorem UtilityProfile.index_nat_lt_add_left_cancel (a b c : UtilityProfile L) (i: Nat) (i_Lt: i < L.length)
    (a_lt_b:
      a.utilities[i]'(by exact Nat_can_index_utilities i a i_Lt)
        < b.utilities[i]'(by exact Nat_can_index_utilities i b i_Lt)
    ):
    (c + a).utilities[i]'(by exact Nat_can_index_utilities i (c + a) i_Lt)
      < (c + b).utilities[i]'(by exact Nat_can_index_utilities i (c + b) i_Lt) := by
  unfold UtilityProfile.add HAdd.hAdd instHAdd Add.add
  obtain ⟨utilities_1, same_length_1⟩ := a
  obtain ⟨utilities_2, same_length_2⟩ := b
  obtain ⟨utilities, same_length⟩ := c
  simp_all only
  rw [same_length] at same_length_1 same_length_2 i_Lt
  symm at same_length_1 same_length_2
  exact index_lt_list_zipWith_left_cancel utilities_1 utilities_2 utilities ⟨i, i_Lt⟩ same_length_1 same_length_2 a_lt_b

instance UtilityProfile.mul : HMul Rat (UtilityProfile L) (UtilityProfile L) where
  hMul x y := by
    let utilities : List Rat := List.map
      (λ u => u * x)
      y.utilities
    let same_length : L.length = utilities.length := by
      unfold utilities
      simp_all only [List.length_map]
      obtain ⟨utilities_1, same_length⟩ := y
      simp_all only
    let up : UtilityProfile L := ⟨utilities, same_length⟩
    exact up

def zero_utility_profile (L: List Type) : UtilityProfile L := by
  let utilities : List Rat := List.map (λ _ => 0) L
  let same_length : L.length = utilities.length := by
    simp_all only [List.length_map, utilities]
  let up : UtilityProfile L := ⟨utilities, same_length⟩
  exact up

-- eval_sp automatically converts a pure strategy utility function to a mixed strategy utility function
def eval_sp (S: MixedStrategyProfile L) (PSUF: PureStrategyProfile L → UtilityProfile L) (acc: PureStrategyProfile L) (id: Fin L.length) : UtilityProfile L := by
  by_cases id_not_last :
    id ≥ ⟨
      L.length - 1,
      by simp_all only [tsub_lt_self_iff, zero_lt_one, and_true]
         exact Fin.pos id
    ⟩
  case pos =>
    let m := S.strategies id
    exact List.foldl
      (λ a b => a + b)
      (zero_utility_profile L)
      (List.map
        (λ a => a.snd *
          (PSUF
            ⟨by
              intro i
              by_cases id_eq_i : id = i
              case pos =>
                  apply Prod.fst at a
                  rw [id_eq_i] at a
                  exact a
              case neg =>
                  exact acc.strategies i
            ⟩
          )
        )
        (List.zip m.strategies m.probabilities)
      )
  case neg =>
    let m := S.strategies id
    exact List.foldl
      (λ a b => a + b)
      (zero_utility_profile L)
      (List.map
        (λ a => a.snd *
          (eval_sp S PSUF
            ⟨by
              intro i
              by_cases id_eq_i : id = i
              case pos =>
                apply Prod.fst at a
                rw [id_eq_i] at a
                exact a
              case neg =>
                  exact acc.strategies i
            ⟩
            ⟨id.val + 1, by
              simp_all
              conv =>
                equals ↑id < L.length - 1 =>
                  simp_all
                  apply Iff.intro
                  · intro _
                    exact id_not_last
                  · intro _
                    exact
                      Nat.add_lt_of_lt_sub
                        id_not_last
              exact id_not_last
            ⟩
          )
        )
        (List.zip m.strategies m.probabilities)
      )
termination_by L.length - id

-- a UtilityFunction is a function that takes a StrategyProfile and returns a Utility
@[aesop safe [constructors, cases]]
inductive UtilityFunction (L: List Type) where
  | mk (x: PureStrategyProfile L → UtilityProfile L) : UtilityFunction L

@[aesop norm unfold]
def UtilityFunction.pure_apply : UtilityFunction L → PureStrategyProfile L → UtilityProfile L
  | mk x => λ p => x p

@[aesop norm unfold]
def UtilityFunction.apply : UtilityFunction L → L.length > 0 → PureStrategyProfile L → MixedStrategyProfile L → UtilityProfile L
  | mk x => λ l psp sp => eval_sp sp x psp ⟨0, l⟩

-- a Game is a number of players, a list of strategies for each player, and a utility function
@[aesop safe [constructors, cases]]
structure Game (L: List Type) where
  (utility: UtilityFunction L)
  (at_least_one_player: List.length L > 0)
  (pure_strategy_profile: PureStrategyProfile L)

def Game.strategy_profile : Game L → MixedStrategyProfile L := by
  intro g
  have psp : PureStrategyProfile L := by exact g.pure_strategy_profile
  let sp : MixedStrategyProfile L := ⟨λ i => PureStrategy.asMixed (psp.strategies i)⟩
  exact sp

-- Game.pure_play executes the game for a given PureStrategyProfile, and returns a list of Utilities
def Game.pure_play : Game L → PureStrategyProfile L → UtilityProfile L :=
  λ g psp => g.utility.pure_apply psp

-- Game.play executes the game for a given StrategyProfile, and returns a list of Utilities
@[aesop norm unfold]
def Game.play : Game L → MixedStrategyProfile L → UtilityProfile L :=
  λ g sp => g.utility.apply
              g.at_least_one_player
              (by exact g.pure_strategy_profile)
              sp

def Game.play_of_pure_eq_pure_play (G: Game L) : (msp: MixedStrategyProfile L) → (pure: msp.isPure) → (G.play msp = G.pure_play (msp.asPure pure)) := by
  intro msp pure
  sorry

-- two strategy profiles are NChange with a list of deltas if those profiles are only possibly
-- different at those deltas
@[aesop norm unfold]
def NChange (L: List Type) (A B: MixedStrategyProfile L) (deltas: List (Fin (List.length L))) : Prop :=
  ∀ (i: Fin (List.length L)), A.strategies i = B.strategies i ∨ deltas.contains i

-- two StrategyProfiles are UnilateralChange if at most one of their players strategies are different
-- (delta is the number of the player whose strategy changed, if one exists)
@[aesop norm unfold]
def UnilateralChange (L: List Type) (A B: MixedStrategyProfile L) (delta: Fin (List.length L)) : Prop :=
  NChange L A B [delta]

-- S does at least as well as S' does at delta
@[aesop norm unfold]
def DoesAtLeastAsWellAs (L: List Type) (G: Game L) (S S': MixedStrategyProfile L) (delta: Fin (List.length L)) : Prop :=
  let thisUtilities: UtilityProfile L := (G.play S)
  let otherUtilities: UtilityProfile L := (G.play S')
  otherUtilities.utilities.get (Fin.cast otherUtilities.same_length delta)
    ≤ thisUtilities.utilities.get (Fin.cast thisUtilities.same_length delta)

def DoesBetterThan  (L: List Type) (G: Game L) (S S': MixedStrategyProfile L) (delta: Fin (List.length L)) : Prop :=
  let thisUtilities: UtilityProfile L := (G.play S)
  let otherUtilities: UtilityProfile L := (G.play S')
  otherUtilities.utilities.get (Fin.cast otherUtilities.same_length delta)
    < thisUtilities.utilities.get (Fin.cast thisUtilities.same_length delta)

-- A StrategyProfile fulfills NashEquilibrium when no player can increase their utility by unilaterally changing their strategy
@[aesop norm unfold]
def NashEquilibrium (L: List Type) (G: Game L) (S: MixedStrategyProfile L) : Prop :=
  -- for every StrategyProfile and delta, if it's a UnilateralChange, S must do at least as well as S' for delta
  ∀ (S': MixedStrategyProfile L)
    (delta: Fin (List.length L)),
    UnilateralChange L S S' delta → DoesAtLeastAsWellAs L G S S' delta

-- A StrategyProfile fulfills StrictNashEquilibrium when no player can increase or keep their utility by unilaterally changing their strategy
def StrictNashEquilibrium (L: List Type) (G: Game L) (S: MixedStrategyProfile L) : Prop :=
  -- for every StrategyProfile and delta, if it's a UnilateralChange, S must outperform S' for delta
  ∀ (S': MixedStrategyProfile L)
    (delta: Fin (List.length L)),
    UnilateralChange L S S' delta → DoesBetterThan L G S S' delta

def GameSymmetric (L: List Type) : Prop := L.Chain' (λ a b => a = b)

def GameFinite (L: List Type) : Prop := L.Forall (λ t => Finite t)

@[simp]
theorem nchange_comm: ∀ (S': MixedStrategyProfile L) (_: NChange L S S' deltas), NChange L S' S deltas := by
  intro S' og
  unfold NChange at og ⊢
  conv => ext i
          pattern S'.strategies i = S.strategies i
          rw [eq_comm]
  exact og

@[simp]
theorem nchange_self: NChange L S S deltas := by
  unfold NChange
  intro i
  left
  rfl

@[simp]
theorem nchange_trans: NChange L S S' deltas1 → NChange L S' S'' deltas2 → NChange L S S'' (deltas1 ++ deltas2) := by
  intro nc1 nc2
  unfold NChange at nc1 nc2 ⊢
  intro i
  specialize nc1 i
  specialize nc2 i
  simp_all only [List.get_eq_getElem, List.elem_eq_mem, decide_eq_true_eq, List.mem_append, Bool.decide_or,
    Bool.or_eq_true]
  cases nc1 with
  | inl h =>
    cases nc2 with
    | inl h_1 => simp_all only [true_or]
    | inr h_2 => simp_all only [or_true]
  | inr h_1 =>
    cases nc2 with
    | inl h => simp_all only [true_or, or_true]
    | inr h_2 => simp_all only [or_self, or_true]

@[simp]
theorem nchange_split: NChange L S S'' (deltas1 ++ deltas2) → ∃ (S': MixedStrategyProfile L), NChange L S S' deltas1 ∧ NChange L S' S'' deltas2 := by
  intro nc
  constructor
  case w =>
    exact ⟨λ x => if deltas2.contains x then S.strategies x else S''.strategies x⟩
  case h =>
    constructor
    case left =>
      intro i
      specialize nc i
      cases nc
      case inl h =>
        simp_all only [List.get_eq_getElem, List.elem_eq_mem, decide_eq_true_eq, ite_self, true_or]
      case inr h =>
        simp_all only [List.elem_eq_mem, List.mem_append, Bool.decide_or, Bool.or_eq_true, decide_eq_true_eq,
          List.get_eq_getElem]
        obtain ⟨strategies⟩ := S
        obtain ⟨strategies_1⟩ := S''
        simp_all only
        cases h with
        | inl h_1 => simp_all only [or_true]
        | inr h_2 => simp_all only [↓reduceIte, true_or]
    case right =>
      intro i
      specialize nc i
      cases nc
      case inl h =>
        simp_all only [List.get_eq_getElem, List.elem_eq_mem, decide_eq_true_eq, ite_self, true_or]
      case inr h =>
        by_cases hdelta : deltas2.contains i
        case pos =>
          simp_all only [List.elem_eq_mem, List.mem_append, Bool.decide_or, Bool.or_eq_true, decide_eq_true_eq,
            List.get_eq_getElem, decide_True, ↓reduceIte, or_true]
        case neg =>
          simp_all only [List.elem_eq_mem, List.mem_append, Bool.decide_or, Bool.or_eq_true, decide_eq_true_eq,
            List.get_eq_getElem, decide_False, Bool.false_eq_true, ↓reduceIte, or_false]

@[simp]
theorem eventually_nchange: ∃ (deltas: List (Fin (List.length L))), NChange L S S' deltas := by
  unfold NChange
  let deltas : List (Fin (List.length L)) := List.finRange (List.length L)
  use deltas
  intro i
  right
  simp_all only [List.elem_eq_mem, List.mem_finRange, decide_True, deltas]

@[simp]
theorem uc_comm: ∀ (S': MixedStrategyProfile L) (_: UnilateralChange L S S' delta), UnilateralChange L S' S delta := by
  intro S' og
  unfold UnilateralChange at og ⊢
  exact nchange_comm S' og

@[simp]
theorem uc_self: UnilateralChange L S S delta := by
  unfold UnilateralChange
  exact nchange_self

@[simp]
theorem uc_trans: UnilateralChange L S S' delta1 → UnilateralChange L S' S'' delta2 → NChange L S S'' [delta1, delta2] := by
  intro uc1 uc2
  unfold UnilateralChange at uc1 uc2
  rw [← List.singleton_append]
  exact nchange_trans uc1 uc2

@[simp]
theorem dalawa_inv: ¬DoesAtLeastAsWellAs L G S S' delta → DoesAtLeastAsWellAs L G S' S delta := by
  intro not_dalawa
  unfold DoesAtLeastAsWellAs at not_dalawa ⊢
  simp_all only [List.get_eq_getElem, Fin.coe_cast, not_le]
  exact le_of_lt not_dalawa

@[simp]
theorem dalawa_self: DoesAtLeastAsWellAs L G S S delta := by
  unfold DoesAtLeastAsWellAs
  simp_all only [List.get_eq_getElem, Fin.coe_cast, le_refl]

theorem dalawa_trans: DoesAtLeastAsWellAs L G S S' delta → DoesAtLeastAsWellAs L G S' S'' delta → DoesAtLeastAsWellAs L G S S'' delta := by
  unfold DoesAtLeastAsWellAs
  intro ss' s's''
  exact
    let thisUtilities := G.play S;
    let otherUtilities := G.play S'';
    Preorder.le_trans (otherUtilities.utilities.get (Fin.cast otherUtilities.same_length delta))
      ((G.play S').utilities.get (Fin.cast (G.play S').same_length delta))
      (thisUtilities.utilities.get (Fin.cast thisUtilities.same_length delta)) s's'' ss'

theorem dbt_imp_dalawa: DoesBetterThan L G S S' delta → DoesAtLeastAsWellAs L G S S' delta := by
  intro dbt
  unfold DoesBetterThan at dbt
  unfold DoesAtLeastAsWellAs
  exact le_of_lt dbt

theorem dbt_trans: DoesBetterThan L G S S' delta → DoesBetterThan L G S' S'' delta → DoesBetterThan L G S S'' delta := by
  unfold DoesBetterThan
  intro ss' s's''
  exact gt_trans ss' s's''

@[simp]
theorem finite_nasheq_exists: GameFinite L → ∃ (S: MixedStrategyProfile L), NashEquilibrium L G S
  := by sorry -- we need to use a fixed point theorem here :p

@[simp]
theorem not_nasheq_if_uc_better: UnilateralChange L A B i ∧ ¬DoesAtLeastAsWellAs L G B A i → ¬NashEquilibrium L G B := by
  intro h ne
  unfold NashEquilibrium at ne
  have uc: UnilateralChange L B A i := by apply And.left at h
                                          apply uc_comm at h
                                          exact h
  apply ne at uc
  let au: UtilityProfile L := (G.play A)
  let bu: UtilityProfile L := (G.play B)
  have greater: au.utilities.get (Fin.cast au.same_length i) > bu.utilities.get (Fin.cast bu.same_length i)
    := by apply And.right at h
          unfold DoesAtLeastAsWellAs at h
          simp_all only [List.get_eq_getElem, Fin.coe_cast, not_le, gt_iff_lt]
  apply not_le_of_gt at greater
  tauto

@[simp]
theorem exists_better_uc_if_not_nasheq:
    ¬NashEquilibrium L G S
      → (∃ (S': MixedStrategyProfile L) (delta: Fin (List.length L)),
          UnilateralChange L S S' delta ∧ DoesAtLeastAsWellAs L G S' S delta) := by
  intro not_ne
  unfold NashEquilibrium at not_ne
  simp_all
  obtain ⟨S', h⟩ := not_ne
  obtain ⟨delta, h⟩ := h
  obtain ⟨left, right⟩ := h
  apply dalawa_inv at right
  use S'
  use delta

@[simp]
theorem better_than_all_ucs_is_nasheq:
    (∀ (S': MixedStrategyProfile L) (delta: Fin (List.length L)),
      UnilateralChange L S S' delta → DoesAtLeastAsWellAs L G S S' delta)
        → NashEquilibrium L G S := by
  intro as'delta
  unfold NashEquilibrium
  intro S' delta uc
  apply as'delta at uc
  exact uc

@[simp]
theorem all_ucs_worse_is_nash_eq:
    (∀ (S': MixedStrategyProfile L) (delta: Fin (List.length L)),
      UnilateralChange L S S' delta → ¬DoesAtLeastAsWellAs L G S' S delta)
        → NashEquilibrium L G S := by
  intro a
  apply better_than_all_ucs_is_nasheq
  intro S' delta uc
  apply a at uc
  exact dalawa_inv uc

-- Example: Prisoner's Dilemma
-- Two prisoners are arrested for a crime. They are held in separate cells and cannot communicate with each other.
-- The prosecutor lacks sufficient evidence to convict the pair on the principal charge, but he has enough to convict both on a lesser charge.
-- Simultaneously, the prosecutor offers each prisoner a bargain. Each prisoner is given the opportunity either to betray the other by
-- testifying that the other committed the crime, or to cooperate with the other by remaining silent.

-- The offer is as follows, where the numbers in parentheses represent the utility, the inverse of the sentence in years:
-- +----------+---------+----------+---------+
-- |          |         | Player 2 |         |
-- +----------+---------+----------+---------+
-- |          |         | Silent   | Confess |
-- | Player 1 | Silent  | 3, 3     | 1, 4    |
-- |          | Confess | 4, 1     | 2, 2    |
-- +----------+---------+----------+---------+

@[aesop safe [constructors, cases]]
inductive PrisonersDilemmaStrategies where
| silent
| confess
deriving BEq, DecidableEq

@[aesop norm unfold]
def PL : List Type := [PrisonersDilemmaStrategies, PrisonersDilemmaStrategies]

def PL_length : List.length PL = 2 := rfl

@[aesop norm unfold]
def PrisonersDilemmaUtilityFunction : UtilityFunction PL :=
  ⟨λ S => match (S.strategies (Fin.ofNat 0)).val, (S.strategies (Fin.ofNat 1)).val with
          | PrisonersDilemmaStrategies.silent,  PrisonersDilemmaStrategies.silent  => { utilities := [3, 3], same_length := rfl }
          | PrisonersDilemmaStrategies.silent,  PrisonersDilemmaStrategies.confess => { utilities := [1, 4], same_length := rfl }
          | PrisonersDilemmaStrategies.confess, PrisonersDilemmaStrategies.silent  => { utilities := [4, 1], same_length := rfl }
          | PrisonersDilemmaStrategies.confess, PrisonersDilemmaStrategies.confess => { utilities := [2, 2], same_length := rfl }
  ⟩

@[aesop norm unfold]
def PrisonersDilemmaPureProfile : PureStrategyProfile PL :=
  { strategies := λ i => match i with
                          | ⟨0, _⟩ => ⟨PrisonersDilemmaStrategies.silent⟩
                          | ⟨1, _⟩ => ⟨PrisonersDilemmaStrategies.silent⟩
  }

@[aesop norm unfold]
def PrisonersDilemmaSilentSilentProfile : MixedStrategyProfile PL :=
  { strategies := λ i => match i with
                          | ⟨0, _⟩ => PureStrategy.asMixed ⟨PrisonersDilemmaStrategies.silent⟩
                          | ⟨1, _⟩ => PureStrategy.asMixed ⟨PrisonersDilemmaStrategies.silent⟩
  }

@[aesop norm unfold]
def PrisonersDilemmaSilentConfessProfile : MixedStrategyProfile PL :=
  { strategies := λ i => match i with
                          | ⟨0, _⟩ => PureStrategy.asMixed ⟨PrisonersDilemmaStrategies.silent⟩
                          | ⟨1, _⟩ => PureStrategy.asMixed ⟨PrisonersDilemmaStrategies.confess⟩
  }

@[aesop norm unfold]
def PrisonersDilemmaConfessConfessProfile : MixedStrategyProfile PL :=
  { strategies := λ i => match i with
                          | ⟨0, _⟩ => PureStrategy.asMixed ⟨PrisonersDilemmaStrategies.confess⟩
                          | ⟨1, _⟩ => PureStrategy.asMixed ⟨PrisonersDilemmaStrategies.confess⟩
  }

@[aesop norm unfold]
def PrisonersDilemmaGame : Game PL :=
{
  utility := PrisonersDilemmaUtilityFunction,
  at_least_one_player := Nat.zero_lt_succ 1
  pure_strategy_profile := by exact PrisonersDilemmaPureProfile
}

theorem PDSilentConfessIsUnilateralOfPDSilentSilent : UnilateralChange PL PrisonersDilemmaSilentConfessProfile PrisonersDilemmaSilentSilentProfile (Fin.mk 1 x) := by
  unfold UnilateralChange
  intro i
  cases i
  case mk val isLt =>
    cases val
    case zero =>  left
                  unfold PrisonersDilemmaSilentSilentProfile
                  unfold PrisonersDilemmaSilentConfessProfile
                  simp_all
    case succ n =>
      cases n
      case zero =>  right
                    simp_all
      case succ m =>  rw [PL_length] at isLt
                      conv at isLt => lhs
                                      change m + 2
                                      rw [add_comm]
                      simp only [add_lt_iff_neg_left, not_lt_zero'] at isLt

theorem NotNashEquilibriumSilentSilent : ¬ NashEquilibrium PL PrisonersDilemmaGame PrisonersDilemmaSilentSilentProfile := by
  apply not_nasheq_if_uc_better
  case i =>
    rw [PL_length]
    exact Fin.last 1
  case a =>
    constructor
    case left => exact PDSilentConfessIsUnilateralOfPDSilentSilent
    case right => unfold PL PrisonersDilemmaGame PrisonersDilemmaSilentSilentProfile
                    PrisonersDilemmaSilentConfessProfile PrisonersDilemmaPureProfile PrisonersDilemmaUtilityFunction
                    DoesAtLeastAsWellAs Game.play UtilityFunction.apply eval_sp PureStrategy.asMixed
                  simp_all [↓dreduceDIte]
                  unfold eval_sp UtilityProfile.mul
                  simp_all [↓reduceDIte]
                  apply UtilityProfile.index_nat_lt_add_left_cancel _ _ (zero_utility_profile [PrisonersDilemmaStrategies, PrisonersDilemmaStrategies]) 1 (by simp_all)
                  simp_all only
                  apply UtilityProfile.index_nat_lt_add_left_cancel _ _ (zero_utility_profile [PrisonersDilemmaStrategies, PrisonersDilemmaStrategies]) 1 (by simp_all)
                  simp_all only [List.getElem_cons_succ, List.getElem_cons_zero]
                  rfl

theorem ConfessConfessDALAWAChangedOne :
    ∀ m: MixedStrategy PrisonersDilemmaStrategies,
      DoesAtLeastAsWellAs PL PrisonersDilemmaGame
        PrisonersDilemmaConfessConfessProfile
        ⟨λ i => match i with
                | ⟨0, _⟩ => m
                | ⟨1, _⟩ => PureStrategy.asMixed ⟨PrisonersDilemmaStrategies.confess⟩⟩
        ⟨0, by unfold PL; simp_all⟩
        := by
  sorry

theorem ConfessConfessDALAWAChangedTwo :
    ∀ m: MixedStrategy PrisonersDilemmaStrategies,
      DoesAtLeastAsWellAs PL PrisonersDilemmaGame
        ⟨λ i => match i with
                | ⟨0, _⟩ => m
                | ⟨1, _⟩ => PureStrategy.asMixed ⟨PrisonersDilemmaStrategies.confess⟩⟩
        PrisonersDilemmaConfessConfessProfile
        ⟨1, by unfold PL; simp_all⟩
        := by
  sorry

theorem NashEquilibriumConfessConfess : NashEquilibrium PL PrisonersDilemmaGame PrisonersDilemmaConfessConfessProfile := by
  apply better_than_all_ucs_is_nasheq
  intro S' delta uc
  have i : Fin PL.length := ⟨0, by simp [PL_length]⟩
  specialize uc i
  match i with
  | ⟨0, _⟩ => sorry
  | ⟨1, _⟩ => sorry

-- Example: Rock-Paper-Scissors

inductive RockPaperScissorsStrategies where
| rock
| paper
| scissors

def RPS : List Type := [RockPaperScissorsStrategies, RockPaperScissorsStrategies]
def RPS_length : List.length RPS = 2 := rfl

def RockPaperScissorsUtilityFunction : UtilityFunction RPS :=
  ⟨λ S => match (S.strategies (Fin.ofNat 0)).val, (S.strategies (Fin.ofNat 1)).val with
          | RockPaperScissorsStrategies.rock,     RockPaperScissorsStrategies.rock     => { utilities := [1, 1], same_length := rfl }
          | RockPaperScissorsStrategies.rock,     RockPaperScissorsStrategies.paper    => { utilities := [0, 2], same_length := rfl }
          | RockPaperScissorsStrategies.rock,     RockPaperScissorsStrategies.scissors => { utilities := [2, 0], same_length := rfl }
          | RockPaperScissorsStrategies.paper,    RockPaperScissorsStrategies.rock     => { utilities := [2, 0], same_length := rfl }
          | RockPaperScissorsStrategies.paper,    RockPaperScissorsStrategies.paper    => { utilities := [1, 1], same_length := rfl }
          | RockPaperScissorsStrategies.paper,    RockPaperScissorsStrategies.scissors => { utilities := [0, 2], same_length := rfl }
          | RockPaperScissorsStrategies.scissors, RockPaperScissorsStrategies.rock     => { utilities := [0, 2], same_length := rfl }
          | RockPaperScissorsStrategies.scissors, RockPaperScissorsStrategies.paper    => { utilities := [2, 0], same_length := rfl }
          | RockPaperScissorsStrategies.scissors, RockPaperScissorsStrategies.scissors => { utilities := [1, 1], same_length := rfl }
  ⟩

def RPSPureProfile : PureStrategyProfile RPS :=
  {
    strategies := λ i => match i with
                          | ⟨0, _⟩ => ⟨RockPaperScissorsStrategies.paper⟩
                          | ⟨1, _⟩ => ⟨RockPaperScissorsStrategies.scissors⟩
  }

def RockPaperScissorsGame : Game RPS :=
  {
    utility := RockPaperScissorsUtilityFunction,
    at_least_one_player := Nat.zero_lt_succ 1
    pure_strategy_profile := by exact RPSPureProfile
  }

-- Example: Nash Demand Game

-- Two players are asked to demand a share of some good. If the sum of the demands is less than or equal to the total amount available,
-- then both players get their demand. Otherwise, neither player gets anything.

structure NashDemandChoice where
  (demand: Rat)
  (demand_nonnegative: demand ≥ 0)
  (demand_le_one: demand ≤ 1)

def NashDemandChoiceList : List Type := [NashDemandChoice, NashDemandChoice]

def NashDemandUtilityFunction : UtilityFunction NashDemandChoiceList :=
  ⟨
    λ S =>
      match S.strategies (Fin.ofNat 0), S.strategies (Fin.ofNat 1) with
      | ⟨d1, _, _⟩, ⟨d2, _, _⟩ =>
        let d12 : Rat := d1 + d2
        let oneUtility : Rat := 1
          if d12 ≤ oneUtility then { utilities := [d1, d2], same_length := rfl }
        else { utilities := [0, 0], same_length := rfl }
  ⟩

def NDC_Pure : PureStrategyProfile NashDemandChoiceList :=
  {
    strategies :=
      λ i =>
        match i with
        | ⟨0, _⟩ => ⟨
          ⟨1, by exact rfl, by exact Preorder.le_refl 1 ⟩
        ⟩
        | ⟨1, _⟩ => ⟨
          ⟨1, by exact rfl, by exact Preorder.le_refl 1 ⟩
        ⟩
  }

def NashDemandGame : Game NashDemandChoiceList :=
  {
    utility := NashDemandUtilityFunction,
    at_least_one_player := Nat.zero_lt_succ 1
    pure_strategy_profile := by exact NDC_Pure
  }

-- Example: Iterated Prisoner's Dilemma for 5 rounds

structure IPD_Strategy where
  (strategy_function: List PrisonersDilemmaStrategies → List PrisonersDilemmaStrategies → PrisonersDilemmaStrategies)

def IPDList : List Type := [IPD_Strategy, IPD_Strategy]

def IPD_UtilityRecurse (psp: PureStrategyProfile IPDList) (p1_list: List PrisonersDilemmaStrategies) (p2_list: List PrisonersDilemmaStrategies) (iter: Nat) : UtilityProfile IPDList := by
  by_cases iter = 0
  case pos => exact zero_utility_profile IPDList
  case neg =>
    let p1_choice : PrisonersDilemmaStrategies := (psp.strategies (Fin.ofNat 0)).val.strategy_function p1_list p2_list
    let p2_choice : PrisonersDilemmaStrategies := (psp.strategies (Fin.ofNat 1)).val.strategy_function p2_list p1_list
    let current_round_utilities :=
      PrisonersDilemmaUtilityFunction.pure_apply
        ⟨λ i => match i with
                | ⟨0, _⟩ => PureStrategy.mk p1_choice
                | ⟨1, _⟩ => PureStrategy.mk p2_choice⟩
    have PL_eq_IPDLLength : PL.length = IPDList.length := by unfold PL
                                                             unfold PL at current_round_utilities
                                                             simp_all
                                                             rfl
    let current_round_utilities_casted := current_round_utilities.cast PL_eq_IPDLLength
    exact current_round_utilities_casted
      + (IPD_UtilityRecurse psp (p1_choice::p1_list) (p2_choice::p2_list) (iter - 1))

def IPD_UtilityFunction : UtilityFunction IPDList :=
  ⟨λ S => IPD_UtilityRecurse S [] [] 5⟩

def AlwaysConfess : IPD_Strategy := ⟨λ _ _ => PrisonersDilemmaStrategies.confess⟩

def AlwaysSilent : IPD_Strategy := ⟨λ _ _ => PrisonersDilemmaStrategies.silent⟩

def TitForTat : IPD_Strategy :=
  ⟨
    λ _ other =>
      match other with
      | [] => PrisonersDilemmaStrategies.silent
      | x :: _ => x
  ⟩

def Alternate : IPD_Strategy :=
  ⟨
    λ self _ =>
      match self with
      | [] => PrisonersDilemmaStrategies.confess
      | x :: _ =>
          if (x = PrisonersDilemmaStrategies.confess) then
            PrisonersDilemmaStrategies.silent
          else
            PrisonersDilemmaStrategies.confess
  ⟩

def BothAlwaysConfess : PureStrategyProfile IPDList :=
  {
    strategies := λ i => match i with
                          | ⟨0, _⟩ => ⟨AlwaysConfess⟩
                          | ⟨1, _⟩ => ⟨AlwaysConfess⟩
  }

def IPDGame : Game IPDList :=
  {
    utility := IPD_UtilityFunction
    at_least_one_player := Nat.zero_lt_succ 1
    pure_strategy_profile := by exact BothAlwaysConfess
  }
