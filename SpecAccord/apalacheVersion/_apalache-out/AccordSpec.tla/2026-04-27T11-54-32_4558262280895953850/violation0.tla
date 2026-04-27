---------------------------- MODULE counterexample ----------------------------

EXTENDS AccordSpec

(* Constant initialization state *)
ConstInit ==
  Bottom = 99
    /\ E = 0
    /\ F = 0
    /\ Id = {1}
    /\ NoProc = 0
    /\ Nop = 0
    /\ NumberOfRecoveryAttempts = 1
    /\ Proc = {1}

(* Initial state [_transition(0)] *)
State0 ==
  Bottom = 99
    /\ Dvar = SetAsFun({<<1, SetAsFun({<<1, {}>>})>>})
    /\ E = 0
    /\ F = 0
    /\ Id = {1}
    /\ NoProc = 0
    /\ Nop = 0
    /\ NumberOfRecoveryAttempts = 1
    /\ Proc = {1}
    /\ Qvar = SetAsFun({<<1, SetAsFun({<<1, {}>>})>>})
    /\ TXvar = SetAsFun({<<1, SetAsFun({<<1, 99>>})>>})
    /\ Wvar = SetAsFun({<<1, SetAsFun({<<1, {}>>})>>})
    /\ abal = SetAsFun({<<1, SetAsFun({<<1, 0>>})>>})
    /\ bal = SetAsFun({<<1, SetAsFun({<<1, 0>>})>>})
    /\ dep = SetAsFun({<<1, SetAsFun({<<1, {}>>})>>})
    /\ initCoord = SetAsFun({<<1, 0>>})
    /\ initTimestamp
      = <<[id |-> 0, t |-> 0], [id |-> 0, t |-> 2], [id |-> 0, t |-> 1]>>
    /\ msgs = {}
    /\ phase = SetAsFun({<<1, SetAsFun({<<1, 1>>})>>})
    /\ postWaitingFlag = SetAsFun({<<1, SetAsFun({<<1, FALSE>>})>>})
    /\ recovered = SetAsFun({<<1, SetAsFun({<<1, 0>>})>>})
    /\ recoveryAttemptBal = SetAsFun({<<1, SetAsFun({<<1, 0>>})>>})
    /\ submitted = {}
    /\ ts = SetAsFun({<<1, SetAsFun({<<1, [id |-> 0, t |-> 0]>>})>>})
    /\ txn = SetAsFun({<<1, SetAsFun({<<1, 99>>})>>})

(* State1 [_transition(16)] *)
State1 ==
  Bottom = 99
    /\ Dvar = SetAsFun({<<1, SetAsFun({<<1, {}>>})>>})
    /\ E = 0
    /\ F = 0
    /\ Id = {1}
    /\ NoProc = 0
    /\ Nop = 0
    /\ NumberOfRecoveryAttempts = 1
    /\ Proc = {1}
    /\ Qvar = SetAsFun({<<1, SetAsFun({<<1, {}>>})>>})
    /\ TXvar = SetAsFun({<<1, SetAsFun({<<1, 99>>})>>})
    /\ Wvar = SetAsFun({<<1, SetAsFun({<<1, {}>>})>>})
    /\ abal = SetAsFun({<<1, SetAsFun({<<1, 0>>})>>})
    /\ bal = SetAsFun({<<1, SetAsFun({<<1, 0>>})>>})
    /\ dep = SetAsFun({<<1, SetAsFun({<<1, {}>>})>>})
    /\ initCoord = SetAsFun({<<1, 1>>})
    /\ initTimestamp
      = <<[id |-> 1, t |-> 0], [id |-> 0, t |-> 2], [id |-> 0, t |-> 1]>>
    /\ msgs
      = {Variant("PreAcceptOKMessage", [body |->
          [Dq |-> {}, id |-> 1, tq |-> [id |-> 1, t |-> 0]],
        from |-> 1,
        to |-> 1])}
    /\ phase = SetAsFun({<<1, SetAsFun({<<1, 2>>})>>})
    /\ postWaitingFlag = SetAsFun({<<1, SetAsFun({<<1, FALSE>>})>>})
    /\ recovered = SetAsFun({<<1, SetAsFun({<<1, 0>>})>>})
    /\ recoveryAttemptBal = SetAsFun({<<1, SetAsFun({<<1, 0>>})>>})
    /\ submitted = {1}
    /\ ts = SetAsFun({<<1, SetAsFun({<<1, [id |-> 1, t |-> 0]>>})>>})
    /\ txn = SetAsFun({<<1, SetAsFun({<<1, 1>>})>>})

(* State2 [_transition(30)] *)
State2 ==
  Bottom = 99
    /\ Dvar = SetAsFun({<<1, SetAsFun({<<1, {}>>})>>})
    /\ E = 0
    /\ F = 0
    /\ Id = {1}
    /\ NoProc = 0
    /\ Nop = 0
    /\ NumberOfRecoveryAttempts = 1
    /\ Proc = {1}
    /\ Qvar = SetAsFun({<<1, SetAsFun({<<1, {}>>})>>})
    /\ TXvar = SetAsFun({<<1, SetAsFun({<<1, 99>>})>>})
    /\ Wvar = SetAsFun({<<1, SetAsFun({<<1, {}>>})>>})
    /\ abal = SetAsFun({<<1, SetAsFun({<<1, 0>>})>>})
    /\ bal = SetAsFun({<<1, SetAsFun({<<1, 1>>})>>})
    /\ dep = SetAsFun({<<1, SetAsFun({<<1, {}>>})>>})
    /\ initCoord = SetAsFun({<<1, 1>>})
    /\ initTimestamp
      = <<[id |-> 1, t |-> 0], [id |-> 0, t |-> 2], [id |-> 0, t |-> 1]>>
    /\ msgs
      = { Variant("PreAcceptOKMessage", [body |->
            [Dq |-> {}, id |-> 1, tq |-> [id |-> 1, t |-> 0]],
          from |-> 1,
          to |-> 1]),
        Variant("RecoverOKMessage", [body |->
            [WPq |-> {},
              Wq |-> {},
              abalq |-> 0,
              b |-> 1,
              depq |-> {},
              id |-> 1,
              phaseq |-> 2,
              rejectq |-> FALSE,
              tq |-> [id |-> 1, t |-> 0],
              txq |-> 1],
          from |-> 1,
          to |-> 1]) }
    /\ phase = SetAsFun({<<1, SetAsFun({<<1, 2>>})>>})
    /\ postWaitingFlag = SetAsFun({<<1, SetAsFun({<<1, FALSE>>})>>})
    /\ recovered = SetAsFun({<<1, SetAsFun({<<1, 1>>})>>})
    /\ recoveryAttemptBal = SetAsFun({<<1, SetAsFun({<<1, 0>>})>>})
    /\ submitted = {1}
    /\ ts = SetAsFun({<<1, SetAsFun({<<1, [id |-> 1, t |-> 0]>>})>>})
    /\ txn = SetAsFun({<<1, SetAsFun({<<1, 1>>})>>})

(* State3 [_transition(47)] *)
State3 ==
  Bottom = 99
    /\ Dvar = SetAsFun({<<1, SetAsFun({<<1, {}>>})>>})
    /\ E = 0
    /\ F = 0
    /\ Id = {1}
    /\ NoProc = 0
    /\ Nop = 0
    /\ NumberOfRecoveryAttempts = 1
    /\ Proc = {1}
    /\ Qvar = SetAsFun({<<1, SetAsFun({<<1, {}>>})>>})
    /\ TXvar = SetAsFun({<<1, SetAsFun({<<1, 99>>})>>})
    /\ Wvar = SetAsFun({<<1, SetAsFun({<<1, {}>>})>>})
    /\ abal = SetAsFun({<<1, SetAsFun({<<1, 1>>})>>})
    /\ bal = SetAsFun({<<1, SetAsFun({<<1, 1>>})>>})
    /\ dep = SetAsFun({<<1, SetAsFun({<<1, {}>>})>>})
    /\ initCoord = SetAsFun({<<1, 1>>})
    /\ initTimestamp
      = <<[id |-> 1, t |-> 0], [id |-> 0, t |-> 2], [id |-> 0, t |-> 1]>>
    /\ msgs
      = { Variant("AcceptOKMessage", [body |-> [Dq |-> {}, b |-> 1, id |-> 1],
          from |-> 1,
          to |-> 1]),
        Variant("PreAcceptOKMessage", [body |->
            [Dq |-> {}, id |-> 1, tq |-> [id |-> 1, t |-> 0]],
          from |-> 1,
          to |-> 1]) }
    /\ phase = SetAsFun({<<1, SetAsFun({<<1, 3>>})>>})
    /\ postWaitingFlag = SetAsFun({<<1, SetAsFun({<<1, FALSE>>})>>})
    /\ recovered = SetAsFun({<<1, SetAsFun({<<1, 1>>})>>})
    /\ recoveryAttemptBal = SetAsFun({<<1, SetAsFun({<<1, 0>>})>>})
    /\ submitted = {1}
    /\ ts = SetAsFun({<<1, SetAsFun({<<1, [id |-> 1, t |-> 0]>>})>>})
    /\ txn = SetAsFun({<<1, SetAsFun({<<1, 0>>})>>})

(* State4 [_transition(26)] *)
State4 ==
  Bottom = 99
    /\ Dvar = SetAsFun({<<1, SetAsFun({<<1, {}>>})>>})
    /\ E = 0
    /\ F = 0
    /\ Id = {1}
    /\ NoProc = 0
    /\ Nop = 0
    /\ NumberOfRecoveryAttempts = 1
    /\ Proc = {1}
    /\ Qvar = SetAsFun({<<1, SetAsFun({<<1, {}>>})>>})
    /\ TXvar = SetAsFun({<<1, SetAsFun({<<1, 99>>})>>})
    /\ Wvar = SetAsFun({<<1, SetAsFun({<<1, {}>>})>>})
    /\ abal = SetAsFun({<<1, SetAsFun({<<1, 1>>})>>})
    /\ bal = SetAsFun({<<1, SetAsFun({<<1, 1>>})>>})
    /\ dep = SetAsFun({<<1, SetAsFun({<<1, {}>>})>>})
    /\ initCoord = SetAsFun({<<1, 1>>})
    /\ initTimestamp
      = <<[id |-> 1, t |-> 0], [id |-> 0, t |-> 2], [id |-> 0, t |-> 1]>>
    /\ msgs
      = { Variant("CommitOKMessage", [body |-> [b |-> 1, id |-> 1],
          from |-> 1,
          to |-> 1]),
        Variant("PreAcceptOKMessage", [body |->
            [Dq |-> {}, id |-> 1, tq |-> [id |-> 1, t |-> 0]],
          from |-> 1,
          to |-> 1]) }
    /\ phase = SetAsFun({<<1, SetAsFun({<<1, 4>>})>>})
    /\ postWaitingFlag = SetAsFun({<<1, SetAsFun({<<1, FALSE>>})>>})
    /\ recovered = SetAsFun({<<1, SetAsFun({<<1, 1>>})>>})
    /\ recoveryAttemptBal = SetAsFun({<<1, SetAsFun({<<1, 0>>})>>})
    /\ submitted = {1}
    /\ ts = SetAsFun({<<1, SetAsFun({<<1, [id |-> 1, t |-> 0]>>})>>})
    /\ txn = SetAsFun({<<1, SetAsFun({<<1, 0>>})>>})

(* State5 [_transition(27)] *)
State5 ==
  Bottom = 99
    /\ Dvar = SetAsFun({<<1, SetAsFun({<<1, {}>>})>>})
    /\ E = 0
    /\ F = 0
    /\ Id = {1}
    /\ NoProc = 0
    /\ Nop = 0
    /\ NumberOfRecoveryAttempts = 1
    /\ Proc = {1}
    /\ Qvar = SetAsFun({<<1, SetAsFun({<<1, {}>>})>>})
    /\ TXvar = SetAsFun({<<1, SetAsFun({<<1, 99>>})>>})
    /\ Wvar = SetAsFun({<<1, SetAsFun({<<1, {}>>})>>})
    /\ abal = SetAsFun({<<1, SetAsFun({<<1, 1>>})>>})
    /\ bal = SetAsFun({<<1, SetAsFun({<<1, 1>>})>>})
    /\ dep = SetAsFun({<<1, SetAsFun({<<1, {}>>})>>})
    /\ initCoord = SetAsFun({<<1, 1>>})
    /\ initTimestamp
      = <<[id |-> 1, t |-> 0], [id |-> 0, t |-> 2], [id |-> 0, t |-> 1]>>
    /\ msgs
      = {Variant("PreAcceptOKMessage", [body |->
          [Dq |-> {}, id |-> 1, tq |-> [id |-> 1, t |-> 0]],
        from |-> 1,
        to |-> 1])}
    /\ phase = SetAsFun({<<1, SetAsFun({<<1, 5>>})>>})
    /\ postWaitingFlag = SetAsFun({<<1, SetAsFun({<<1, FALSE>>})>>})
    /\ recovered = SetAsFun({<<1, SetAsFun({<<1, 1>>})>>})
    /\ recoveryAttemptBal = SetAsFun({<<1, SetAsFun({<<1, 0>>})>>})
    /\ submitted = {1}
    /\ ts = SetAsFun({<<1, SetAsFun({<<1, [id |-> 1, t |-> 0]>>})>>})
    /\ txn = SetAsFun({<<1, SetAsFun({<<1, 0>>})>>})

(* The following formula holds true in the last state and violates the invariant *)
InvariantViolation == TRUE

================================================================================
(* Created by Apalache on Mon Apr 27 11:54:55 CEST 2026 *)
(* https://github.com/apalache-mc/apalache *)
