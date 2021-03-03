---- MODULE Saga ----
EXTENDS TLC

CONSTANTS server, Worker
ASSUME
    /\ Worker /= {}
    /\ ~(server \in Worker)

RemoteValue == {"init", "accepted", "cancelled", "aborted"}
Status == {"init", "requesting", "responsed",
    "waiting-aborted", "aborted", "committed"}
LocalValue == {"init", "ok"}

(*--algorithm Saga
variables
    remote_value = "init",
    status = "init",
    local_value = "init";

process serverProc = server

begin
StartRequest:
    status := "requesting";
RPC:
    either
        if remote_value = "init" then
            remote_value := "accepted";
        else
            goto Done;
        end if;
    or
        if remote_value = "init" then
            remote_value := "cancelled";
        end if;
        goto Done;
    or
        goto Done;
    end either;
Responsed:
    if status /= "requesting" then
        goto Done;
    else
        status := "responsed";
    end if;
DBWrite:
    if status = "responsed" then
        local_value := "ok";
        status := "committed";
    end if;
end process;

process worker \in Worker
begin
StartWorker:
    while TRUE do
    CheckStatus:
        if status \in {"aborted", "committed"} then
            goto Done;
        elsif status = "init" then
            goto StartWorker;
        elsif status = "responsed" then
            goto WorkerWaitAbort;
        elsif status = "waiting-aborted" then
            goto AbortSaga;
        end if;

    WorkerRPC:
        if remote_value = "init" then
            either
                remote_value := "cancelled";
                goto DBWriteAborted;
            or
                remote_value := "accepted";
            end either;
        elsif remote_value \in {"cancelled", "aborted"} then
            goto DBWriteAborted;
        end if;

    WorkerReponsed:
        if status = "requesting" then
            status := "responsed";
            goto AbortSaga;
        else
            goto StartWorker;
        end if;

    WorkerWaitAbort:
        if status = "responsed" then
            status := "waiting-aborted";
            goto AbortSaga;
        else
            goto StartWorker;
        end if;

    AbortSaga:
        remote_value := "aborted";

    DBWriteAborted:
        either
            status := "aborted";
            goto Done;
        or
            goto StartWorker;
        end either;
    end while;
end process;

end algorithm;
*)
\* BEGIN TRANSLATION (chksum(pcal) = "ece3ff65" /\ chksum(tla) = "f3aa3bec")
VARIABLES remote_value, status, local_value, pc

vars == << remote_value, status, local_value, pc >>

ProcSet == {server} \cup (Worker)

Init == (* Global variables *)
        /\ remote_value = "init"
        /\ status = "init"
        /\ local_value = "init"
        /\ pc = [self \in ProcSet |-> CASE self = server -> "StartRequest"
                                        [] self \in Worker -> "StartWorker"]

StartRequest == /\ pc[server] = "StartRequest"
                /\ status' = "requesting"
                /\ pc' = [pc EXCEPT ![server] = "RPC"]
                /\ UNCHANGED << remote_value, local_value >>

RPC == /\ pc[server] = "RPC"
       /\ \/ /\ IF remote_value = "init"
                   THEN /\ remote_value' = "accepted"
                        /\ pc' = [pc EXCEPT ![server] = "Responsed"]
                   ELSE /\ pc' = [pc EXCEPT ![server] = "Done"]
                        /\ UNCHANGED remote_value
          \/ /\ IF remote_value = "init"
                   THEN /\ remote_value' = "cancelled"
                   ELSE /\ TRUE
                        /\ UNCHANGED remote_value
             /\ pc' = [pc EXCEPT ![server] = "Done"]
          \/ /\ pc' = [pc EXCEPT ![server] = "Done"]
             /\ UNCHANGED remote_value
       /\ UNCHANGED << status, local_value >>

Responsed == /\ pc[server] = "Responsed"
             /\ IF status /= "requesting"
                   THEN /\ pc' = [pc EXCEPT ![server] = "Done"]
                        /\ UNCHANGED status
                   ELSE /\ status' = "responsed"
                        /\ pc' = [pc EXCEPT ![server] = "DBWrite"]
             /\ UNCHANGED << remote_value, local_value >>

DBWrite == /\ pc[server] = "DBWrite"
           /\ IF status = "responsed"
                 THEN /\ local_value' = "ok"
                      /\ status' = "committed"
                 ELSE /\ TRUE
                      /\ UNCHANGED << status, local_value >>
           /\ pc' = [pc EXCEPT ![server] = "Done"]
           /\ UNCHANGED remote_value

serverProc == StartRequest \/ RPC \/ Responsed \/ DBWrite

StartWorker(self) == /\ pc[self] = "StartWorker"
                     /\ pc' = [pc EXCEPT ![self] = "CheckStatus"]
                     /\ UNCHANGED << remote_value, status, local_value >>

CheckStatus(self) == /\ pc[self] = "CheckStatus"
                     /\ IF status \in {"aborted", "committed"}
                           THEN /\ pc' = [pc EXCEPT ![self] = "Done"]
                           ELSE /\ IF status = "init"
                                      THEN /\ pc' = [pc EXCEPT ![self] = "StartWorker"]
                                      ELSE /\ IF status = "responsed"
                                                 THEN /\ pc' = [pc EXCEPT ![self] = "WorkerWaitAbort"]
                                                 ELSE /\ IF status = "waiting-aborted"
                                                            THEN /\ pc' = [pc EXCEPT ![self] = "AbortSaga"]
                                                            ELSE /\ pc' = [pc EXCEPT ![self] = "WorkerRPC"]
                     /\ UNCHANGED << remote_value, status, local_value >>

WorkerRPC(self) == /\ pc[self] = "WorkerRPC"
                   /\ IF remote_value = "init"
                         THEN /\ \/ /\ remote_value' = "cancelled"
                                    /\ pc' = [pc EXCEPT ![self] = "DBWriteAborted"]
                                 \/ /\ remote_value' = "accepted"
                                    /\ pc' = [pc EXCEPT ![self] = "WorkerReponsed"]
                         ELSE /\ IF remote_value \in {"cancelled", "aborted"}
                                    THEN /\ pc' = [pc EXCEPT ![self] = "DBWriteAborted"]
                                    ELSE /\ pc' = [pc EXCEPT ![self] = "WorkerReponsed"]
                              /\ UNCHANGED remote_value
                   /\ UNCHANGED << status, local_value >>

WorkerReponsed(self) == /\ pc[self] = "WorkerReponsed"
                        /\ IF status = "requesting"
                              THEN /\ status' = "responsed"
                                   /\ pc' = [pc EXCEPT ![self] = "AbortSaga"]
                              ELSE /\ pc' = [pc EXCEPT ![self] = "StartWorker"]
                                   /\ UNCHANGED status
                        /\ UNCHANGED << remote_value, local_value >>

WorkerWaitAbort(self) == /\ pc[self] = "WorkerWaitAbort"
                         /\ IF status = "responsed"
                               THEN /\ status' = "waiting-aborted"
                                    /\ pc' = [pc EXCEPT ![self] = "AbortSaga"]
                               ELSE /\ pc' = [pc EXCEPT ![self] = "StartWorker"]
                                    /\ UNCHANGED status
                         /\ UNCHANGED << remote_value, local_value >>

AbortSaga(self) == /\ pc[self] = "AbortSaga"
                   /\ remote_value' = "aborted"
                   /\ pc' = [pc EXCEPT ![self] = "DBWriteAborted"]
                   /\ UNCHANGED << status, local_value >>

DBWriteAborted(self) == /\ pc[self] = "DBWriteAborted"
                        /\ \/ /\ status' = "aborted"
                              /\ pc' = [pc EXCEPT ![self] = "Done"]
                           \/ /\ pc' = [pc EXCEPT ![self] = "StartWorker"]
                              /\ UNCHANGED status
                        /\ UNCHANGED << remote_value, local_value >>

worker(self) == StartWorker(self) \/ CheckStatus(self) \/ WorkerRPC(self)
                   \/ WorkerReponsed(self) \/ WorkerWaitAbort(self)
                   \/ AbortSaga(self) \/ DBWriteAborted(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == serverProc
           \/ (\E self \in Worker: worker(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

TypeOK ==
    /\ remote_value \in RemoteValue
    /\ status \in Status
    /\ local_value \in LocalValue

Inv ==
    /\ local_value = "ok" => status = "committed" /\ remote_value = "accepted"

InvWorker ==
    /\ status = "aborted" => remote_value = "aborted" \/ remote_value = "cancelled"

Completed ==
    /\ (\A p \in ProcSet: pc[p] = "Done") => status = "committed" \/ status = "aborted"

Term == local_value /= "ok"

Perms == Permutations(Worker)

====
