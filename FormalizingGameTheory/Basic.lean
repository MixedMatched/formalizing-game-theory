import Mathlib.Data.Real.Basic
import Aesop

-- a Utility is a Real number representing the payoff of a given set of strategies
structure Utility := (val : Real)

instance : Add Utility := ⟨λ u v => ⟨u.val + v.val⟩⟩
instance : LE Utility := ⟨λ u v => u.val ≤ v.val⟩
instance : LT Utility := ⟨λ u v => u.val < v.val⟩
instance : OfNat Utility n := ⟨⟨n⟩⟩

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
  (utilities: List Utility)
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

-- NashEquilibrium is a StrategyProfile where no player can increase their utility by unilaterally changing their strategy
def NashEquilibrium (L: List Type) (N: Nat) (G: Game L N) (S: StrategyProfile L) : Prop :=
  ∀ (i: Fin (List.length L))
    (s': Strategy (List.get L i)),
    let newStrategies : (f: Fin (List.length L)) → Strategy (List.get L f) :=
      λ j => if h : i = j then by { rw [h] at s'; exact s' }
                          else S.strategies j
    let newStrategyProfile : StrategyProfile L := { strategies := @newStrategies }
    let UNew : UtilityProfile L := PlayGame L N G newStrategyProfile
    let UOld : UtilityProfile L := PlayGame L N G S
    (List.get UNew.utilities (Fin.cast UNew.same_length i)) ≤ (List.get UOld.utilities (Fin.cast UOld.same_length i))

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
-- | Player 1 | Silent  | 4, 4     | 1, 6    |
-- |          | Confess | 6, 1     | 2, 2    |
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
                    | PrisonersDilemmaStrategies.silent,  PrisonersDilemmaStrategies.silent  => { utilities := [4, 4], same_length := rfl }
                    | PrisonersDilemmaStrategies.silent,  PrisonersDilemmaStrategies.confess => { utilities := [1, 6], same_length := rfl }
                    | PrisonersDilemmaStrategies.confess, PrisonersDilemmaStrategies.silent  => { utilities := [6, 1], same_length := rfl }
                    | PrisonersDilemmaStrategies.confess, PrisonersDilemmaStrategies.confess => { utilities := [2, 2], same_length := rfl }
                  | _, _ => { utilities := [0, 0], same_length := rfl }
  }

def PrisonersDilemmaGame : Game PL 2 :=
  { utility := PrisonersDilemmaUtilityFunction,
    same_length := rfl,
    at_least_one_player := Nat.zero_lt_succ 1
  }

def PrisonersDilemmaSilentProfile : StrategyProfile PL :=
  { strategies := λ i => match i with
                          | ⟨0, _⟩ => Strategy.pure ⟨PrisonersDilemmaStrategies.silent⟩
                          | ⟨1, _⟩ => Strategy.pure ⟨PrisonersDilemmaStrategies.silent⟩
  }

theorem NotNashEquilibriumSilent : ¬ NashEquilibrium PL 2 PrisonersDilemmaGame PrisonersDilemmaSilentProfile
  := by intro h
        unfold NashEquilibrium at h
        unfold PrisonersDilemmaSilentProfile at h
        unfold PlayGame at h
        unfold UtilityFunction.val at h
        unfold PrisonersDilemmaGame at h
        unfold PrisonersDilemmaUtilityFunction at h
        simp_all
        let x : Fin (List.length PL) := ⟨0, by exact Nat.succ_pos (List.length [PrisonersDilemmaStrategies])⟩
        have PLxPDS : PureStrategy (List.get PL x) = PureStrategy PrisonersDilemmaStrategies := by simp_all
                                                                                                   conv => lhs
                                                                                                           arg 1
                                                                                                           change PrisonersDilemmaStrategies
        let s'' : Strategy (List.get PL x) := Strategy.pure ⟨PrisonersDilemmaStrategies.confess⟩
        let h' : _ := h x s''
        repeat simp at h'
        conv at h' => rhs
                      rhs
                      change Fin.ofNat 0
                      change 0
        simp at h'
        unfold StrategyProfile.strategies at h'
        conv at h' => lhs
                      rhs
                      change Fin.ofNat 0
                      change 0
        sorry


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
                      let d12 : Utility := ⟨d1 + d2⟩
                      let oneUtility : Utility := ⟨1⟩
                        if d12 ≤ oneUtility then { utilities := [⟨d1⟩, ⟨d2⟩], same_length := rfl }
                      else { utilities := [0, 0], same_length := rfl }
                  | _, _ => { utilities := [0, 0], same_length := rfl }
  }

noncomputable def NashDemandGame : Game NashDemandChoiceList 2 :=
  { utility := NashDemandUtilityFunction,
    same_length := rfl,
    at_least_one_player := Nat.zero_lt_succ 1
  }
