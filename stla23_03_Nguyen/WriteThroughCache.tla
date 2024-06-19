------------------ MODULE WriteThroughCache ------------------
EXTENDS Naturals, Sequences, MemoryInterface 
VARIABLES wmem, ctl, buf, cache, memQ 
CONSTANT QLen
ASSUME (QLen \in Nat) /\ (QLen > 0) 
M == INSTANCE InternalMemory WITH mem <- wmem
--------------------------------------------------------------
Init == /\ M!IInit 
        /\ cache = [p \in Proc |-> [a \in Adr |-> NoVal] ]
        /\ memQ = << >>  
 
TypeInvariant == 
  /\ wmem  \in [Adr -> Val]
  /\ ctl   \in [Proc -> {"rdy", "busy", "waiting", "done"}] 
  /\ buf   \in [Proc -> MReq \cup Val \cup {NoVal}]
  /\ cache \in [Proc -> [Adr -> Val \cup {NoVal}]] 
  /\ memQ  \in Seq(Proc \X MReq) 

Coherence == \A p, q \in Proc, a \in Adr : 
                (NoVal \notin {cache[p][a], cache[q][a]})
                      => (cache[p][a]=cache[q][a]) 
--------------------------------------------------------------
Req(p) == M!Req(p) /\ UNCHANGED <<cache, memQ>> 
Rsp(p) == M!Rsp(p) /\ UNCHANGED <<cache, memQ>> 

RdMiss(p) ==  /\ (ctl[p] = "busy") /\ (buf[p].op = "Rd") 
              /\ cache[p][buf[p].adr] = NoVal 
              /\ Len(memQ) < QLen
              /\ memQ' = Append(memQ, <<p, buf[p]>>)
              /\ ctl' = [ctl EXCEPT ![p] = "waiting"]
              /\ UNCHANGED <<memInt, wmem, buf, cache>>

DoRd(p) == 
  /\ ctl[p] \in {"busy","waiting"} 
  /\ buf[p].op = "Rd" 
  /\ cache[p][buf[p].adr] # NoVal
  /\ buf' = [buf EXCEPT ![p] = cache[p][buf[p].adr]]
  /\ ctl' = [ctl EXCEPT ![p] = "done"]
  /\ UNCHANGED <<memInt, wmem, cache, memQ>> 

DoWr(p) == 
  LET r == buf[p]
  IN  /\ (ctl[p] = "busy") /\ (r.op = "Wr") 
      /\ Len(memQ) < QLen
      /\ cache' = [q \in Proc |-> 
                    IF (p=q)  \/  (cache[q][r.adr]#NoVal)
                      THEN [cache[q] EXCEPT ![r.adr] = r.val]
                      ELSE cache[q] ]
      /\ memQ' = Append(memQ, <<p, r>>)
      /\ buf' = [buf EXCEPT ![p] = NoVal]
      /\ ctl' = [ctl EXCEPT ![p] = "done"]
      /\ UNCHANGED <<memInt, wmem>> 

vmem  ==  
  LET f[i \in 0 .. Len(memQ)] == 
        IF i=0 THEN wmem
               ELSE IF memQ[i][2].op = "Rd"
                      THEN f[i-1]
                      ELSE [f[i-1] EXCEPT ![memQ[i][2].adr] =
                                              memQ[i][2].val]
  IN f[Len(memQ)] 

MemQWr == LET r == Head(memQ)[2] 
          IN  /\ (memQ # << >>)  /\   (r.op = "Wr") 
              /\ wmem' = [wmem EXCEPT ![r.adr] = r.val] 
              /\ memQ' = Tail(memQ) 
              /\ UNCHANGED <<memInt, buf, ctl, cache>> 

MemQRd == 
  LET p == Head(memQ)[1] 
      r == Head(memQ)[2] 
  IN  /\ (memQ # << >> ) /\ (r.op = "Rd")
      /\ memQ' = Tail(memQ)
      /\ cache' = [cache EXCEPT ![p][r.adr] = vmem[r.adr]]
      /\ UNCHANGED <<memInt, wmem, buf, ctl>>  

Evict(p,a) == /\ (ctl[p] = "waiting") => (buf[p].adr # a) 
              /\ cache' = [cache EXCEPT ![p][a] = NoVal]
              /\ UNCHANGED <<memInt, wmem, buf, ctl, memQ>> 

Next == \/ \E p\in Proc : \/ Req(p) \/ Rsp(p) 
                          \/ RdMiss(p) \/ DoRd(p) \/ DoWr(p) 
                          \/ \E a \in Adr : Evict(p, a)
        \/ MemQWr \/ MemQRd    

Spec == 
  Init /\ [][Next]_<<memInt, wmem, buf, ctl, cache, memQ>>
--------------------------------------------------------------
THEOREM Spec => [](TypeInvariant /\ Coherence)
--------------------------------------------------------------
LM == INSTANCE Memory 
THEOREM Spec => LM!Spec

(************************************************************)
(* The following is for the TLC model checker.              *)
(* It is not needed for the TLA+ proof.                     *)
(************************************************************)

(***************************************************************************)
(* The operator Send is used in specifications in conjuncts of the form    *)
(*                                                                         *)
(* (+)  Send(p, d, memInt, memInt')                                        *)
(*                                                                         *)
(* to specify the new value of memInt.  For TLC to handle such a           *)
(* conjunct, the definition of Send must make (+) equal something of the   *)
(* form                                                                    *)
(*                                                                         *)
(*   memInt' = ...                                                         *)
(*                                                                         *)
(* (A similar observation holds for Reply.)  We define Send so that (+)    *)
(* equals                                                                  *)
(*                                                                         *)
(*   memInt' = <<p, d>>                                                    *)
(*                                                                         *)
(* If we were doing serious model checking, we might try to reduce         *)
(* the state space by letting the value of memInt remain constant,         *)
(* so we would define Send so that (+) equals                              *)
(*                                                                         *)
(*   memInt' = memInt.                                                     *)
(***************************************************************************)
MCSend(p, d, oldMemInt, newMemInt)  ==  newMemInt = <<p, d>>
MCReply(p, d, oldMemInt, newMemInt) ==  newMemInt = <<p, d>>

(***************************************************************************)
(* We define MCInitMemInt, the set of initial values of memInt, to contain *)
(* the single element <<p, NoVal>>, for an arbitrary processor p.          *)
(***************************************************************************)
MCInitMemInt == {<<CHOOSE p \in Proc : TRUE, NoVal>>}

(***************************************************************************)
(* As described in the section titled "Proving Implementation", the        *)
(* write-through cache specifies Spec satisfies                            *)
(*                                                                         *)
(*    Spec => LM!Inner(omem, octl, obuf)!ISpec                             *)
(*                                                                         *)
(* for the following choices of omem, octl, and obuf:                      *)
(***************************************************************************)

   omem == vmem
   octl == [p \in Proc |-> IF ctl[p] = "waiting" THEN "busy" ELSE ctl[p]]
   obuf == buf

LM_Inner_TypeInvariant == LM!Inner(omem, octl, obuf)!TypeInvariant
LM_Inner_ISpec == /\ LM!Inner(omem, octl, obuf)!IInit 
                  /\ [][LM!Inner(omem, octl, obuf)!INext]_<<memInt, omem, octl, obuf>>
==============================================================
