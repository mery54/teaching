---------------------------- MODULE pluscalil269q ----------------------
EXTENDS Integers, Sequences,TLC
CONSTANTS input,max

ASSUME max \in Nat /\ max # 0 /\ input \subseteq -max..max 

inputs == {1,2,3,4,5,6,7,8}

(*--algorithm tri 
variables 
    A = inputs,
    SA = {}, va = 0,
    SB = {}, vb = 0,
    chanA = <<>>,
    chanB = <<>>;
    v = 0;
    
process P = "P"
variable x;
begin
    SendLoop:
    while A # {} do
        x := CHOOSE e \in A : TRUE;
        A := A \ {x};
        v := v +x;
        if x % 2 = 0 then
            chanA := Append(chanA, x);
        else
            chanB := Append(chanB, x);
        end if;
    end while;
end process;

process AProc = "A"
variable y;
begin
    ReceiveA:
    while TRUE do
        await Len(chanA) > 0;
        y := Head(chanA);
        chanA := Tail(chanA);
    	SA := SA \cup {y};
	va := va + y;
     end while;
 end process;

process BProc = "B"
variable z;
begin
    ReceiveB:
    while TRUE do
        await Len(chanB) > 0;
        z := Head(chanB);
        chanB := Tail(chanB);
        SB := SB \cup {z};
	vb := vb + z;
    end while;
end process;

end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "da0847bd" /\ chksum(tla) = "e2c2be44")
CONSTANT defaultInitValue
VARIABLES A, SA, va, SB, vb, chanA, chanB, v, pc, x, y, z

vars == << A, SA, va, SB, vb, chanA, chanB, v, pc, x, y, z >>

ProcSet == {"P"} \cup {"A"} \cup {"B"}

Init == (* Global variables *)
        /\ A = inputs
        /\ SA = {}
        /\ va = 0
        /\ SB = {}
        /\ vb = 0
        /\ chanA = <<>>
        /\ chanB = <<>>
        /\ v = 0
        (* Process P *)
        /\ x = defaultInitValue
        (* Process AProc *)
        /\ y = defaultInitValue
        (* Process BProc *)
        /\ z = defaultInitValue
        /\ pc = [self \in ProcSet |-> CASE self = "P" -> "SendLoop"
                                        [] self = "A" -> "ReceiveA"
                                        [] self = "B" -> "ReceiveB"]

SendLoop == /\ pc["P"] = "SendLoop"
            /\ IF A # {}
                  THEN /\ x' = (CHOOSE e \in A : TRUE)
                       /\ A' = A \ {x'}
                       /\ v' = v +x'
                       /\ IF x' % 2 = 0
                             THEN /\ chanA' = Append(chanA, x')
                                  /\ chanB' = chanB
                             ELSE /\ chanB' = Append(chanB, x')
                                  /\ chanA' = chanA
                       /\ pc' = [pc EXCEPT !["P"] = "SendLoop"]
                  ELSE /\ pc' = [pc EXCEPT !["P"] = "Done"]
                       /\ UNCHANGED << A, chanA, chanB, v, x >>
            /\ UNCHANGED << SA, va, SB, vb, y, z >>

P == SendLoop

ReceiveA == /\ pc["A"] = "ReceiveA"
            /\ Len(chanA) > 0
            /\ y' = Head(chanA)
            /\ chanA' = Tail(chanA)
            /\ SA' = (SA \cup {y'})
            /\ va' = va + y'
            /\ pc' = [pc EXCEPT !["A"] = "ReceiveA"]
            /\ UNCHANGED << A, SB, vb, chanB, v, x, z >>

AProc == ReceiveA

ReceiveB == /\ pc["B"] = "ReceiveB"
            /\ Len(chanB) > 0
            /\ z' = Head(chanB)
            /\ chanB' = Tail(chanB)
            /\ SB' = (SB \cup {z'})
            /\ vb' = vb + z'
            /\ pc' = [pc EXCEPT !["B"] = "ReceiveB"]
            /\ UNCHANGED << A, SA, va, chanA, v, x, y >>

BProc == ReceiveB

Next == P \/ AProc \/ BProc

Spec == Init /\ [][Next]_vars

\* END TRANSLATION 




PC == pc["A"]="done" /\ pc["B"]="done" /\ pc["P"]="done"  => v=va+vb
TEST  == \E self \in ProcSet: pc[self] # "Done"

====
