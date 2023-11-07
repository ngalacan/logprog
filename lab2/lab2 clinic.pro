implement main
    open core, stdio, file

domains
    diagnosis = a; b; c; d; e.

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
    exam : (string X, string Date, integer Doc) nondeterm anyflow.
clauses
    exam(X, Date, Doc) :-
        patient(Xid, X, _, _, _),
        appointment(Doc, Xid, Date, _, _, _).

%возраст
class predicates
    age : (string X [out], integer Age [out]) nondeterm.
clauses
    age(X, Age) :-
        patient(_, X, _, _, Age).

%молодые люди
class predicates
    young_people : (string X [out], integer Age [out]) nondeterm.
clauses
    young_people(X, Age) :-
        age(X, Age),
        Age < 40,
        write(X, " ", Age),
        nl.

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

clauses
    run() :-
        consult("../base.txt", clinic),
        fail.

    run() :-
        write("\nДиагнозы пациента 1: \n"),
        show_diagnosis(1, _Name, D),
        write(D),
        nl,
        fail.

    run() :-
        write("\nПациенты с диагнозом d: \n"),
        show_diagnosis(_, Name, d),
        write(Name),
        nl,
        fail.

    run() :-
        write("\nКому выдан больничный: \n"),
        sick_leave(_, Name, _),
        write(Name),
        nl,
        fail.

    run() :-
        write("\nМедосмотры: \n"),
        exam(Pat, Date, Doc),
        write(Date, " ", Doc, " ", Pat),
        nl,
        fail.

    run() :-
        write("\nМедосмотры врача 33 за все время: \n"),
        exam(Pat, Date, 33),
        write(Date, " ", Pat),
        nl,
        fail.

    run() :-
        write("\nМолодые люди: \n"),
        young_people(_, _),
        fail.

    run() :-
        write("\nДанные записанных к терапевту: \n"),
        data_of_registered(Xid, X, A, T, G, "терапевт"),
        write(Xid, " ", X, " ", A, " ", T, " ", G),
        nl,
        fail.

    run() :-
        write("\nК каким врачам записан Сидоров: \n"),
        registered_to("Сидоров", _Doc),
        fail.

    run() :-
        write("\nСтоимость лекарств пациента 2: \n"),
        treatment_prices(2, Med, N),
        write(Med, " ", N),
        nl,
        fail.

    run() :-
        write("\nСтоимость лечения пациента 2: \n"),
        treatment_cost(2),
        nl,
        fail.

    run().

end implement main

goal
    console::runUTF8(main::run).
