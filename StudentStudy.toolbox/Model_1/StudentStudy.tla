---------------------------- MODULE StudentStudy ----------------------------
EXTENDS Sequences, Naturals, TLC

(*
--algorithm StudyRooms
  variables Students = {"A", "B", "C", "D", "E", "F", "G", "H"};
            Waiting = {};
            Occupants = {};
            spaces = 3;

  process person \in Students 
  begin study:
    either await spaces>0 ;
          spaces := spaces-1;
          Occupants := Occupants \union {self};
          print Occupants;
    or Occupants := Occupants \ {self};
       spaces := spaces +1;
    end either
  end process

end algorithm
*)
\* BEGIN TRANSLATION
VARIABLES Students, Waiting, Occupants, spaces, pc

vars == << Students, Waiting, Occupants, spaces, pc >>

ProcSet == (Students)

Init == (* Global variables *)
        /\ Students = {"A", "B", "C", "D", "E", "F", "G", "H"}
        /\ Waiting = {}
        /\ Occupants = {}
        /\ spaces = 3
        /\ pc = [self \in ProcSet |-> "study"]

study(self) == /\ pc[self] = "study"
               /\ \/ /\ spaces>0
                     /\ spaces' = spaces-1
                     /\ Occupants' = (Occupants \union {self})
                     /\ PrintT(Occupants')
                  \/ /\ Occupants' = Occupants \ {self}
                     /\ spaces' = spaces +1
               /\ pc' = [pc EXCEPT ![self] = "Done"]
               /\ UNCHANGED << Students, Waiting >>

person(self) == study(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Students: person(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Tue Oct 22 12:01:04 BST 2019 by alun
\* Created Tue Oct 22 11:53:07 BST 2019 by alun
