implement main
    open core, stdio, file

domains
    diagnosis = a; b; c; d; e.
    ilist = integer*.

class facts - clinic
    patient : (integer Id, string Name, string Address, string Tel, integer Age).
    doctor : (integer Id, string Name, string Spec).
    appointment : (integer Did, integer Pid, string Date, diagnosis D, string Med, boolean Boln).
    queue : (integer Pid, string Spec, string Date).
    price : (string Med, integer P).
    s : (integer S) single.

clauses
    s(0).

%диагноз
class predicates
    show_diagnosis : (integer Xid, string X, diagnosis D) nondeterm anyflow.
clauses
    show_diagnosis(Xid, X, D) :-
        patient(Xid, X, _, _, _),
        appointment(_, Xid, _, D, _, _).

%больничный
class predicates
    sick_leave : (integer Xid [out], string X [out], integer Doc [out]) nondeterm.
clauses
    sick_leave(Xid, X, Doc) :-
        patient(Xid, X, _, _, _),
        appointment(Doc, Xid, _, _, _, true).

%медосмотр
class predicates
    exam : (integer Doc) nondeterm.
clauses
    exam(Doc) :-
        appointment(Doc, Xid, Date, _, _, _),
        patient(Xid, X, _, _, Age),
        write(X, " ", Age, " ", Date).

%средний возраст
class predicates
    length : (A*) -> integer N.
    sum : (real* List) -> real Sum.
    average : (real* List) -> real Average determ.
    average_age : (integer DocId) -> real Av nondeterm.

clauses
    length([]) = 0.
    length([_ | T]) = length(T) + 1.

    sum([]) = 0.
    sum([H | T]) = sum(T) + H.

    average(L) = sum(L) / length(L) :-
        length(L) > 0.

    average_age(Doc) =
            average(
                [ Age ||
                    appointment(Doc, Xid, _, _, _, _),
                    patient(Xid, _, _, _, Age)
                ]) :-
        doctor(Doc, _, _).

%молодые люди
class predicates
    young_people : () -> ilist Age nondeterm.
clauses
    young_people() =
            [ Age ||
                patient(_, X, _, _, Age),
                Age < 40
            ] :-
        patient(_, X, _, _, Age),
        Age < 40,
        write(X).

%данные записанного
class predicates
    data_of_registered : (integer Xid [out], string X [out], string A [out], string T [out], integer G [out], string Doc [in]) nondeterm.
clauses
    data_of_registered(Xid, X, A, T, G, Doc) :-
        patient(Xid, X, A, T, G),
        queue(Xid, Doc, _).

%к кому записан
class predicates
    registered_to : (string X [in], string Doc [out]) nondeterm.
clauses
    registered_to(X, Doc) :-
        patient(Xid, X, _, _, _),
        queue(Xid, Doc, _),
        write(Doc),
        nl.

%цены назначенных лекарств
class predicates
    treatment_prices : (integer Xid, string Med [out], integer N [out]) nondeterm.
clauses
    treatment_prices(Xid, Med, N) :-
        appointment(_, Xid, _, _, Med, _),
        price(Med, N).

%стоимость лечения (сумма)
class predicates
    treatment_cost : (integer Xid).
clauses
    treatment_cost(Xid) :-
        assert(s(0)),
        treatment_prices(Xid, _, N),
        s(Sum),
        assert(s(Sum + N)),
        fail.

    treatment_cost(_Xid) :-
        s(Sum),
        write(Sum),
        nl.

%cтоимость лечения (сумма элементов списка)
class predicates
    total_cost : (integer Xid) -> real Price nondeterm.
clauses
    total_cost(Xid) = sum([ Price || treatment_prices(Xid, _, Price) ]) :-
        patient(Xid, _, _, _, _).

%кол-во пациентов с больничным
class predicates
    sick_leave_num : () -> integer Num.
clauses
    sick_leave_num() =
        length(
            [ Xid ||
                patient(Xid, _, _, _, _),
                appointment(_, Xid, _, _, _, true)
            ]).

clauses
    run() :-
        consult("../base.txt", clinic),
        fail.

    run() :-
        write("\nКому выдан больничный: \n"),
        sick_leave(_, Name, _),
        write(Name),
        nl,
        fail.

    run() :-
        write("\nКоличество пациентов с больничным: \n"),
        write(sick_leave_num()),
        nl,
        fail.

    run() :-
        write("\nМедосмотры у офтальмолога: \n"),
        exam(11),
        nl,
        fail.

    run() :-
        write("\nСредний возраст пациентов офтальмолога: \n"),
        write(average_age(11)),
        nl,
        fail.

    run() :-
        write("\nМолодые люди: \n"),
        write(young_people(), "\n"),
        fail.

    run() :-
        write("\nЦены лекарств пациента 1: \n"),
        treatment_prices(1, Med, N),
        write(Med, " ", N),
        nl,
        fail.

    run() :-
        write("\nСтоимость лечения пациента 1: \n"),
        treatment_cost(1),
        fail.

    run() :-
        write("\nСтоимость лечения пациента 1: \n"),
        write(total_cost(1)),
        fail.

    run().

end implement main

goal
    console::runUTF8(main::run).
