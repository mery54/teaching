---------------------------- MODULE pluscalil269 ----------------------
EXTENDS Integers, Sequences,TLC
CONSTANTS input,max,eod

ASSUME max \in Nat /\ max # 0 /\ input \subseteq -max..max  /\ eod \notin -max..max /\ eod \in Nat

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
    chanA := Append(chanA, eod);
    chanB := Append(chanB, eod);
end process;

process AProc = "A"
variable y;
begin
    ReceiveA:
    while TRUE do
        await Len(chanA) > 0;
        y := Head(chanA);
        chanA := Tail(chanA);
	if y # eod then
    	   SA := SA \cup {y};
	   	va := va + y;
	else
		goto fin;
	end if;	
 
    end while;
    fin:print "fin de A";
end process;

process BProc = "B"
variable z;
begin
    ReceiveB:
    while TRUE do
        await Len(chanB) > 0;
        z := Head(chanB);
        chanB := Tail(chanB);
	if z # eod then
	        SB := SB \cup {z};
			vb := vb + z;
	else
		goto fin;
	end if;
		
	
    end while;
    fin:print "fin de B";
end process;

end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "590c6dcd" /\ chksum(tla) = "f850d9dc")
\* Label fin of process AProc at line 52 col 9 changed to fin_
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
                  ELSE /\ chanA' = Append(chanA, eod)
                       /\ chanB' = Append(chanB, eod)
                       /\ pc' = [pc EXCEPT !["P"] = "Done"]
                       /\ UNCHANGED << A, v, x >>
            /\ UNCHANGED << SA, va, SB, vb, y, z >>

P == SendLoop

ReceiveA == /\ pc["A"] = "ReceiveA"
            /\ Len(chanA) > 0
            /\ y' = Head(chanA)
            /\ chanA' = Tail(chanA)
            /\ IF y' # eod
                  THEN /\ SA' = (SA \cup {y'})
                       /\ va' = va + y'
                       /\ pc' = [pc EXCEPT !["A"] = "ReceiveA"]
                  ELSE /\ pc' = [pc EXCEPT !["A"] = "fin_"]
                       /\ UNCHANGED << SA, va >>
            /\ UNCHANGED << A, SB, vb, chanB, v, x, z >>

fin_ == /\ pc["A"] = "fin_"
        /\ PrintT("fin de A")
        /\ pc' = [pc EXCEPT !["A"] = "Done"]
        /\ UNCHANGED << A, SA, va, SB, vb, chanA, chanB, v, x, y, z >>

AProc == ReceiveA \/ fin_

ReceiveB == /\ pc["B"] = "ReceiveB"
            /\ Len(chanB) > 0
            /\ z' = Head(chanB)
            /\ chanB' = Tail(chanB)
            /\ IF z' # eod
                  THEN /\ SB' = (SB \cup {z'})
                       /\ vb' = vb + z'
                       /\ pc' = [pc EXCEPT !["B"] = "ReceiveB"]
                  ELSE /\ pc' = [pc EXCEPT !["B"] = "fin"]
                       /\ UNCHANGED << SB, vb >>
            /\ UNCHANGED << A, SA, va, chanA, v, x, y >>

fin == /\ pc["B"] = "fin"
       /\ PrintT("fin de B")
       /\ pc' = [pc EXCEPT !["B"] = "Done"]
       /\ UNCHANGED << A, SA, va, SB, vb, chanA, chanB, v, x, y, z >>

BProc == ReceiveB \/ fin

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == P \/ AProc \/ BProc
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 



PC == pc["A"]="done" /\ pc["B"]="done" /\ pc["P"]="done"  => v=va+vb
TEST  == \E self \in ProcSet: pc[self] # "Done"

====
