:- module('thrift', [parse_file/2, parse_chunk/2,
                     doc_header/2, doc_body/2,
                     include_val/2,
                     cpp_include_val/2,
                     ns_scope/2, ns_id/2,
                     literal_val/2,
                     const_type/2, const_id/2, const_val/2,
                     typedef_type/2, typedef_id/2,
                     enum_id/2, enum_entries/2,
                     senum_id/2, senum_entries/2,
                     fields_entires/2,
                     service_id/2, service_extends/2, service_functions/2,
                     func_ow/2, func_type/2, func_id/2, func_sig/2, func_throw/2,
                     map_ctype/2, map_ktype/2, map_vtype/2,
                     set_ctype/2, set_vtype/2,
                     list_ctype/2, list_vtype/2]).

:- meta_predicate
       parse_file(+, -),
       parse_chunk(+, -).

:- use_module(library(record)).
:- use_module(library(error)).

:- dynamic doc_header/2, doc_body/2,
           include_val/2,
           cpp_include_val/2,
           ns_scope/2, ns_id/2,
           literal_val/2,
           const_type/2, const_id/2, const_val/2,
           typedef_type/2, typedef_id/2,
           enum_id/2, enum_entries/2,
           senum_id/2, senum_entries/2,
           fields_entires/2,
           service_id/2, service_extends/2, service_functions/2,
           func_ow/2, func_type/2, func_id/2, func_sig/2, func_throw/2,
           map_ctype/2, map_ktype/2, map_vtype/2,
           set_ctype/2, set_vtype/2,
           list_ctype/2, list_vtype/2.

:- record doc(header:list, body:list).
:- record include(val).
:- record cpp_include(val).
:- record ns(scope, id).
:- record literal(val).
:- record const(type, id, val).
:- record typedef(type, id).
:- record enum(id, entries:list).
:- record senum(id, entries:list).
:- record fields(entries:list).
:- record service(id, extends:list, functions:list(func)).
:- record func(ow, type, id, sig:list, throw:list).
:- record map(ctype, ktype, vtype).
:- record set(ctype, vtype).
:- record list(ctype, vtype).

ecsymf(X)             --> [X], { member(X, `.-`) ; code_type(X, csymf) }.
csymf(X)              --> [X], { code_type(X, csymf) }.
csym(X)               --> [X], { [X] = `.` ; code_type(X, csym) }.
end([])               --> [].
digit(X)              --> [X], { code_type(X, digit) }.
digits_list([X | Xs]) --> digit(X), digits_list(Xs), !.
digits_list([X])      --> digit(X).
digits(Ds)            --> digits_list(Dl), { number_codes(Ds, Dl) }.

named(Name, Id) --> Name, o, id(Id).
opt(Name, yes)  --> Name, s, !.
opt(_, no)      --> s.
wrapped(A, Z, Pred) --> A, s, Pred, s, Z.

comment_body  --> "*/" | [_], comment_body.
comment       --> "/*", comment_body.
scomment_body --> nl | [_], scomment_body.
scomment      --> "//", scomment_body.
comments      --> comment, m, comments | scomment, m, comments | comment | scomment.

nl    --> "\n", nl | "\r", nl | "\n" | "\r".
white --> " " | "\t" | "\r" | "\n".
w     --> white, w | white.
m     --> w, ! | [].
s     --> m, comments, m | m.
o     --> w, comments, m | w.
sep   --> o | m, ",", m | m, ";", m.

document(doc(Header, Body))   --> s, headers(Header), s, definitions(Body).
headers([X | Xs])             --> header(X), headers(Xs), !.
headers(X)                    --> header([X]) | end(X).
header(Out)                   --> include(Out) | cpp_include(Out) | namespace(Out).
include(include(Out))         --> "include", o, literal(Out), o.
cpp_include(cpp_include(Out)) --> "cpp_include", o, literal(Out), o.

namespace(namespace(Scope, Id)) -->
    (
        "namespace", o,
        (
            namespace_scope(Scope), o, id(Id) |
            "smalltalk.category", o, st_id(Id), { Scope = smalltalk } |
            "smalltalk.prefix", o, id(Id), { Scope = smalltalk }
        )
        | "php_namespace", o, literal(Id), { Scope = php }
        | "xsd_namespace", o, literal(Id), { Scope = xsd }
    ), o.

namespace_scope(Out) -->
    (
        "*", { Out = '*' }
        | "cpp", { Out = cpp }
        | "java", { Out = java }
        | "py", { Out = py }
        | "perl", { Out = perl }
        | "rb", { Out = rb }
        | "cocoa", { Out = cocoa }
        | "csharp", { Out = csharp }
    ).

no_apos([])          --> "'".
no_apos([X | Xs])    --> [X], no_quote(Xs).
no_quote([])         --> "\"".
no_quote([X | Xs])   --> [X], no_quote(Xs).
literal(literal(NQ)) --> "\"", no_quote(NQ) | "'", no_apos(NQ).

ident_tail([X | Xs]) --> csym(X), ident_tail(Xs), !.
ident_tail(X)        --> csym([X]) | end(X).
id(Id)               --> csymf(X), !, ( ident_tail(Xs), ! | end(Xs) ), { atom_codes(Id, [X | Xs]) }.

st_ident_tail([X | Xs]) --> ecsym(X), st_ident_tail(Xs), !.
st_ident_tail(X)        --> ecsym([X]) | end(X).
st_id(Id)               --> csymf(X), !, st_ident_tail(Xs), { atom_codes(Id, [X | Xs]) }.

definition(X) -->
    const(X)
    | typedef(X)
    | enum(X)
    | senum(X)
    | struct(X)
    | union(X)
    | exception(X)
    | service(X).
definitions([X | Xs]) --> definition(X), definitions(Xs), !.
definitions([]) --> [].

const(const(Type, Id, Value)) -->
    "const", o, field_type(Type), o, id(Id),
    s, "=", s, const_val(Value), sep.

typedef(typedef(Type, Id)) -->
    "typedef", o, definition_type(Type), o, id(Id), o.

xsd_all --> o, "xsd_all" | s .

enum_entries([(Id:Val) | Xs]) -->
    %% TODO: What happens if some values are set, but others arent?
    %% TODO: What happens if values repeat?
    %% TODO: Is there a convention for numbering ``anonymous'' values?
    id(Id), s, ( "=", s, int_const(Val) | [] ), 
    sep, !, enum_entries(Xs).
enum_entries([]) --> [].
entries(Entries) --> s, wrapped("{", "}", enum_entries(Entries)), s.
enum(enum(Id, Entries)) --> named("enum", Id), entries(Entries).
senum(senum(Id, Entries)) --> named("senum", Id), entries(Entries).

fields([X | Xs])        --> field(X), sep, fields(Xs), !.
fields([X])             --> field(X), !.
fields([])              --> sep | [].
sfields(fields(Fields)) --> wrapped("{", "}", fields(Fields)), s.

struct(struct(Id, Fields))   --> named("struct", Id), xsd_all, sfields(Fields).
union(union(Id, Fields))     --> named("union", Id), xsd_all, sfields(Fields).
exception(union(Id, Fields)) --> named("exception", Id), s, sfields(Fields).

extends([Id])       --> o, "extends", s, wrapped("(", ")", id(Id)), s.
extends([])         --> o.
functions([X | Xs]) --> function(X), sep, functions(Xs), !.
functions([X])      --> function(X).
functions([])       --> sep | [].
service(service(Id, Extends, Functions)) -->
    named("service", Id), extends(Extends), wrapped("{", "}", functions(Functions)).

field_id(Id)              --> int_const(Id), s, ":".
field_id(unset)           --> [].
field_req(optional)       --> "optional", !.
field_req(required)       --> "required", ! | [].
field_val(Val)            --> s, "=", s, const_val(Val).
field_val(unset)          --> [].
field_modifiers(FId, Req) --> field_id(FId), s, field_req(Req), s.
field(field(FId, Req, Type, Id, Val)) -->
    field_modifiers(FId, Req), field_type(Type), o, id(Id), field_val(Val).

xsd_attrs(Atts) --> "xsd_attrs", o, fields(Atts), !.
xsd_attrs([]) --> [].

xsd_field_options(xsd_field_opts(Opt, Nil, Atts)) -->
    opt("xsd_optional", Opt), opt("xsd_nillable", Nil), xsd_atts(Atts).

throws(Throws) --> "throws", s, wrapped("(", ")", fields(Throws)).
throws([]) --> [].
function_type(Type) --> field_type(Type).
function_type(void) --> "void".
function(function(Oneway, Type, Id, Sig, Throws)) -->
    opt("oneway", Oneway), function_type(Type), o, id(Id), s,
    wrapped("(", ")", fields(Sig)), s, throws(Throws).

field_type(Type) --> id(Type) | base_type(Type) | container_type(Type).
definition_type(Type) --> base_type(Type) | container_type(Type).

base_type(bool)   --> "bool".
base_type(byte)   --> "byte".
base_type(i8)     --> "i8".
base_type(i16)    --> "i16".
base_type(i32)    --> "i32".
base_type(i64)    --> "i64".
base_type(double) --> "double".
base_type(string) --> "string".
base_type(slist)  --> "slist".

tparam(T)                  --> wrapped("<", ">", field_type(T)).
tparam(K, V)               --> wrapped("<", ">", (field_type(K), s, ",", s, field_type(V))).
cpp_type(Type)             --> o, "ccp_type", o, literal(Type).
cpp_type([])               --> [].
container_type(Type)       --> map_type(Type) | set_type(Type) | list_type(Type).
map_type(map(CType, K, V)) --> "map", cpp_type(CType), s, tparam(K, V).
set_type(set(CType, K))    --> "set", cpp_type(CType), tparam(K).
list_type(list(CType, K))  --> "list", s, tparam(K), cpp_type(CType).

const_val(Val) -->
    int_const(Val)
    | double_const(Val)
    | literal(Val)
    | id(Val)
    | const_list(Val)
    | const_map(Val).

int_const(Val) -->
    "-", digits(Ds), !, { Val is Ds * -1 }
    | ( "+" | [] ), digits(Val).

double_const(Val) -->
    "-", digits(Ds), mantisa(Man), exponent(Exp),
    { append(Res, [Ds, Man, Exp]), number_codes([45 | Res], Val) }
    | ( "+" | [] ), digits(Ds), mantisa(Man), exponent(Exp),
      { append(Res, [Ds, Man, Exp]), number_codes(Res, Val) }.

consts([X | Xs]) --> const_val(X), sep, !, consts(Xs).
consts([])       --> [].
const_list(Val)  --> wrapped("[", "]", consts(Val)).

mconsts([(K:V) | Xs]) --> const_val(K), s, ":", s, const_val(V), !, mconsts(Xs).
mconsts([])           --> [].
const_map(Val)        --> wrapped("{", "}", mconsts(Val)).

parse_chunk(G, S) :-
    stream_to_lazy_list(S, L),
    phrase(G, L, X),
    findall(E, (member(E, X), ground(E)), X1),
    string_codes(C, X1),
    format('was able to parse to: ~w~n', [C]).

process_chunk(F, G) :-
    setup_call_cleanup(open(F, read, S, []), parse_chunk(G, S), close(S)).

parse_file(File, Parse) :- process_chunk(File, document(Parse)).
