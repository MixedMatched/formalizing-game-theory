import Mathlib.Data.Real.Basic
import Aesop

-- a Utility is a Real number representing the payoff of a given set of strategies

-- a PureStrategy is an instance of the strategy type
structure PureStrategy (A : Type) := (val : A)

-- a MixedStrategy is a probability distribution over PureStrategies
structure MixedStrategy (A : Type) :=
  (strategies: List A)
  (probabilities: List Real)
  (probabilities_sum_to_one: List.foldl (a + b) 0 probabilities = 1)
  (same_length: List.length strategies = List.length probabilities)

-- a Strategy is either a PureStrategy or a MixedStrategy
inductive Strategy (A : Type) where
| pure : PureStrategy A → Strategy A
| mixed : MixedStrategy A → Strategy A

-- a StrategyProfile is a list of strategies (for type reasons, we need to use a function)
structure StrategyProfile (L: List Type) where
  (strategies: (i: Fin (List.length L)) → Strategy (List.get L i))

-- a UtilityProfile is a list of utilities
structure UtilityProfile (L: List Type) where
  (utilities: List Real)
  (same_length: List.length L = List.length utilities)

-- a UtilityFunction is a function that takes a StrategyProfile and returns a Utility
structure UtilityFunction (L: List Type) where
  (val: StrategyProfile L → UtilityProfile L)

-- a Game is a number of players, a list of strategies for each player, and a utility function
structure Game (L: List Type) (N: Nat) where
  (utility: UtilityFunction L)
  (same_length: (List.length L) = N)
  (at_least_one_player: N > 0)

-- a PlayGame is a function that takes a Game, a StrategyProfile, and returns a list of Utilities
def PlayGame (L: List Type) (N: Nat) (G: Game L N) (S: StrategyProfile L) : UtilityProfile L := G.utility.val S

def UnilateralChange (L: List Type) (A B: StrategyProfile L) (delta: Fin (List.length L)) : Prop :=
  ∀ (i: Fin (List.length L)), A.strategies i = B.strategies i ∨ i = delta

theorem UnilateralChangeComm (L: List Type) (S: StrategyProfile L) (delta: Fin (List.length L)):
  ∀ (S': StrategyProfile L)
    (_: UnilateralChange L S S' delta),
    UnilateralChange L S' S delta
    := by intro S' og
          unfold UnilateralChange at og ⊢
          conv => ext i
                  pattern S'.strategies i = S.strategies i
                  rw [eq_comm]
          exact og

-- NashEquilibrium is a StrategyProfile where no player can increase their utility by unilaterally changing their strategy
def NashEquilibrium (L: List Type) (N: Nat) (G: Game L N) (S: StrategyProfile L) : Prop :=
  ∀ (S': StrategyProfile L)
    (delta: Fin (List.length L)),
    let thisUtilities: UtilityProfile L := (PlayGame L N G S)
    let otherUtilities: UtilityProfile L := (PlayGame L N G S')
    UnilateralChange L S S' delta → otherUtilities.utilities.get (Fin.cast otherUtilities.same_length delta) ≤ thisUtilities.utilities.get (Fin.cast thisUtilities.same_length delta)

theorem notNashEqIfBetterStrat : ∀ (L: List Type) (N: Nat) (G: Game L N) (A B: StrategyProfile L) (i: Fin (List.length L)),
  let AUtilities: UtilityProfile L := (PlayGame L N G A)
  let BUtilities: UtilityProfile L := (PlayGame L N G B)
  UnilateralChange L A B i ∧ AUtilities.utilities.get (Fin.cast AUtilities.same_length i) > BUtilities.utilities.get (Fin.cast BUtilities.same_length i) → ¬NashEquilibrium L N G B
  := by intro l n g a b i au bu h ne
        unfold NashEquilibrium at ne
        have uc: UnilateralChange l b a i := by apply And.left at h
                                                apply UnilateralChangeComm at h
                                                exact h
        apply ne at uc
        have greater: (PlayGame l n g a).utilities.get (Fin.cast au.same_length i) > (PlayGame l n g b).utilities.get (Fin.cast bu.same_length i) := by apply And.right at h
                                                                                                                                                        exact h
        apply not_le_of_gt at greater
        tauto

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

inductive PrisonersDilemmaStrategies where
| silent
| confess

def PL : List Type := [PrisonersDilemmaStrategies, PrisonersDilemmaStrategies]
def PL_length : List.length PL = 2 := rfl

def PrisonersDilemmaUtilityFunction : UtilityFunction PL :=
  { val := λ S => match S.strategies (Fin.ofNat 0), S.strategies (Fin.ofNat 1) with
                  | Strategy.pure s1, Strategy.pure s2 =>
                    have h1 : PureStrategy (List.get PL (Fin.ofNat 0)) = PureStrategy PrisonersDilemmaStrategies := rfl
                    have h2 : PureStrategy (List.get PL (Fin.ofNat 1)) = PureStrategy PrisonersDilemmaStrategies := rfl
                    let s1' : PureStrategy PrisonersDilemmaStrategies := by { rw [←h1]; exact s1 }
                    let s2' : PureStrategy PrisonersDilemmaStrategies := by { rw [←h2]; exact s2 }
                    match s1'.val, s2'.val with
                    | PrisonersDilemmaStrategies.silent,  PrisonersDilemmaStrategies.silent  => { utilities := [3, 3], same_length := rfl }
                    | PrisonersDilemmaStrategies.silent,  PrisonersDilemmaStrategies.confess => { utilities := [1, 4], same_length := rfl }
                    | PrisonersDilemmaStrategies.confess, PrisonersDilemmaStrategies.silent  => { utilities := [4, 1], same_length := rfl }
                    | PrisonersDilemmaStrategies.confess, PrisonersDilemmaStrategies.confess => { utilities := [2, 2], same_length := rfl }
                  | _, _ => { utilities := [0, 0], same_length := rfl }
  }

def PrisonersDilemmaGame : Game PL 2 :=
  { utility := PrisonersDilemmaUtilityFunction,
    same_length := rfl,
    at_least_one_player := Nat.zero_lt_succ 1
  }

def PrisonersDilemmaSilentSilentProfile : StrategyProfile PL :=
  { strategies := λ i => match i with
                          | ⟨0, _⟩ => Strategy.pure ⟨PrisonersDilemmaStrategies.silent⟩
                          | ⟨1, _⟩ => Strategy.pure ⟨PrisonersDilemmaStrategies.silent⟩
  }

def PrisonersDilemmaSilentConfessProfile : StrategyProfile PL :=
  { strategies := λ i => match i with
                          | ⟨0, _⟩ => Strategy.pure ⟨PrisonersDilemmaStrategies.silent⟩
                          | ⟨1, _⟩ => Strategy.pure ⟨PrisonersDilemmaStrategies.confess⟩
  }

theorem PDSilentConfessIsUnilateralOfPDSilentSilent : UnilateralChange PL PrisonersDilemmaSilentConfessProfile PrisonersDilemmaSilentSilentProfile (Fin.mk 1 x)
  := by unfold UnilateralChange
        intro i
        cases i
        case mk val isLt =>
          cases val
          case zero => left
                       unfold PrisonersDilemmaSilentSilentProfile
                       unfold PrisonersDilemmaSilentConfessProfile
                       simp_all
          case succ n =>
            cases n
            case zero => right
                         simp_all
            case succ m => rw [PL_length] at isLt
                           conv at isLt => lhs
                                           change m + 2
                                           rw [add_comm]
                           simp_all only [add_zero, add_lt_iff_neg_left, not_lt_zero']

theorem NotNashEquilibriumSilent : ¬ NashEquilibrium PL 2 PrisonersDilemmaGame PrisonersDilemmaSilentSilentProfile
  := by apply notNashEqIfBetterStrat PL 2 PrisonersDilemmaGame PrisonersDilemmaSilentConfessProfile PrisonersDilemmaSilentSilentProfile (Fin.mk 1 _)
        pick_goal 2
        rw [PL_length]
        simp
        constructor
        case left => exact PDSilentConfessIsUnilateralOfPDSilentSilent
        case right => unfold PlayGame PrisonersDilemmaGame PrisonersDilemmaSilentConfessProfile PrisonersDilemmaSilentSilentProfile PrisonersDilemmaUtilityFunction
                      simp_all
                      conv => rhs
                              equals 3 + 1 => exact Eq.symm three_add_one_eq_four
                      simp_all only [lt_add_iff_pos_right, zero_lt_one]

-- Example: Rock-Paper-Scissors

inductive RockPaperScissorsStrategies where
| rock
| paper
| scissors

def RPS : List Type := [RockPaperScissorsStrategies, RockPaperScissorsStrategies]
def RPS_length : List.length RPS = 2 := rfl

def RockPaperScissorsUtilityFunction : UtilityFunction RPS :=
  { val := λ S => match S.strategies (Fin.ofNat 0), S.strategies (Fin.ofNat 1) with
                  | Strategy.pure s1, Strategy.pure s2 =>
                    have h1 : PureStrategy (List.get RPS (Fin.ofNat 0)) = PureStrategy RockPaperScissorsStrategies := rfl
                    have h2 : PureStrategy (List.get RPS (Fin.ofNat 1)) = PureStrategy RockPaperScissorsStrategies := rfl
                    let s1' : PureStrategy RockPaperScissorsStrategies := by { rw [←h1]; exact s1 }
                    let s2' : PureStrategy RockPaperScissorsStrategies := by { rw [←h2]; exact s2 }
                    match s1'.val, s2'.val with
                    | RockPaperScissorsStrategies.rock,     RockPaperScissorsStrategies.rock     => { utilities := [1, 1], same_length := rfl }
                    | RockPaperScissorsStrategies.rock,     RockPaperScissorsStrategies.paper    => { utilities := [0, 2], same_length := rfl }
                    | RockPaperScissorsStrategies.rock,     RockPaperScissorsStrategies.scissors => { utilities := [2, 0], same_length := rfl }
                    | RockPaperScissorsStrategies.paper,    RockPaperScissorsStrategies.rock     => { utilities := [2, 0], same_length := rfl }
                    | RockPaperScissorsStrategies.paper,    RockPaperScissorsStrategies.paper    => { utilities := [1, 1], same_length := rfl }
                    | RockPaperScissorsStrategies.paper,    RockPaperScissorsStrategies.scissors => { utilities := [0, 2], same_length := rfl }
                    | RockPaperScissorsStrategies.scissors, RockPaperScissorsStrategies.rock     => { utilities := [0, 2], same_length := rfl }
                    | RockPaperScissorsStrategies.scissors, RockPaperScissorsStrategies.paper    => { utilities := [2, 0], same_length := rfl }
                    | RockPaperScissorsStrategies.scissors, RockPaperScissorsStrategies.scissors => { utilities := [1, 1], same_length := rfl }
                  | _, _ => { utilities := [0, 0], same_length := rfl }
  }

def RockPaperScissorsGame : Game RPS 2 :=
  { utility := RockPaperScissorsUtilityFunction,
    same_length := rfl,
    at_least_one_player := Nat.zero_lt_succ 1
  }



-- Example: Nash Demand Game

-- Two players are asked to demand a share of some good. If the sum of the demands is less than or equal to the total amount available,
-- then both players get their demand. Otherwise, neither player gets anything.

structure NashDemandChoice where
  (demand: Real)
  (demand_nonnegative: demand ≥ 0)
  (demand_le_one: demand ≤ 1)

def NashDemandChoiceList : List Type := [NashDemandChoice, NashDemandChoice]

noncomputable def NashDemandUtilityFunction : UtilityFunction NashDemandChoiceList :=
  { val := λ S => match S.strategies (Fin.ofNat 0), S.strategies (Fin.ofNat 1) with
                  | Strategy.pure s1, Strategy.pure s2 =>
                    have h1 : PureStrategy (List.get NashDemandChoiceList (Fin.ofNat 0)) = PureStrategy NashDemandChoice := rfl
                    have h2 : PureStrategy (List.get NashDemandChoiceList (Fin.ofNat 1)) = PureStrategy NashDemandChoice := rfl
                    let s1' : PureStrategy NashDemandChoice := by { rw [←h1]; exact s1 }
                    let s2' : PureStrategy NashDemandChoice := by { rw [←h2]; exact s2 }
                    match s1', s2' with
                    | ⟨d1, _, _⟩, ⟨d2, _, _⟩ =>
                      let d12 : Real := d1 + d2
                      let oneUtility : Real := 1
                        if d12 ≤ oneUtility then { utilities := [d1, d2], same_length := rfl }
                      else { utilities := [0, 0], same_length := rfl }
                  | _, _ => { utilities := [0, 0], same_length := rfl }
  }

noncomputable def NashDemandGame : Game NashDemandChoiceList 2 :=
  { utility := NashDemandUtilityFunction,
    same_length := rfl,
    at_least_one_player := Nat.zero_lt_succ 1
  }
