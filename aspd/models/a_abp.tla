------------------- MODULE a_abp -------------------
EXTENDS Naturals, Sequences
CONSTANTS Data
VARIABLES msgQ, ackQ, sBit, sAck, rBit, sent, rcvd  

ABInit == /\ msgQ = << >>
          /\ ackQ = << >>
          /\ sBit \in {0, 1}
          /\ sAck = sBit
          /\ rBit = sBit
          /\ sent = << >>
          /\ rcvd = << >>

TypeInv == /\ msgQ \in Seq({0,1} \X Data)
           /\ ackQ \in Seq({0,1})
           /\ sBit \in {0, 1}
           /\ sAck \in {0, 1}
           /\ rBit \in {0, 1}
           /\ sent \in Seq(Data)
           /\ rcvd \in Seq(Data)

SndNewValue(d) == /\ sAck = sBit
                  /\ sent' = Append(sent, d)
                  /\ sBit' = 1 - sBit
                  /\ msgQ' = Append(msgQ, <<sBit', d>>)
                  /\ UNCHANGED <<ackQ, sAck, rBit, rcvd>>

ReSndMsg == 
  /\ sAck # sBit
  /\ msgQ' = Append(msgQ, <<sBit, sent[Len(sent)]>>)
  /\ UNCHANGED <<ackQ, sBit, sAck, rBit, sent, rcvd>>

RcvMsg == 
  /\ msgQ # <<>>
  /\ msgQ' = Tail(msgQ)
  /\ rBit' = Head(msgQ)[1] 
  /\ rcvd' = IF rBit' # rBit THEN Append(rcvd, Head(msgQ)[2])
                             ELSE rcvd
  /\ UNCHANGED <<ackQ, sBit, sAck, sent>>

SndAck == /\ ackQ' = Append(ackQ, rBit)
          /\ UNCHANGED <<msgQ, sBit, sAck, rBit, sent, rcvd>>

RcvAck == /\ ackQ # << >>
          /\ ackQ' = Tail(ackQ)
          /\ sAck' = Head(ackQ)
          /\ UNCHANGED <<msgQ, sBit, rBit, sent, rcvd>>

Lose(c) == 
   /\ c # << >>
   /\ \E i \in 1..Len(c) : 
       c' = [j \in 1..(Len(c)-1) |-> IF j \leq i THEN c[j] 
                                                 ELSE c[j+1] ]
   /\ UNCHANGED <<sBit, sAck, rBit, sent, rcvd>>

LoseMsg == Lose(msgQ) /\ UNCHANGED ackQ

LoseAck == Lose(ackQ) /\ UNCHANGED msgQ

ABNext == \/ \E d \in Data : SndNewValue(d)
          \/ ReSndMsg \/ RcvMsg \/ SndAck \/ RcvAck
          \/ LoseMsg \/ LoseAck

vars == << msgQ, ackQ, sBit, sAck, rBit, sent, rcvd>>
-------------------------------------------------------------- 
Spec == ABInit /\ [][ABNext]_vars
--------------------------------------------------------------
Inv == /\ Len(rcvd) \in {Len(sent)-1, Len(sent)}
       /\ \A i \in 1..Len(rcvd) : rcvd[i] = sent[i]
       /\ Len(rcvd)# 5 

Init == ABInit
Next == ABNext

test == rcvd # <<"deux","deux">>
==============================================================
