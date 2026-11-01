# proofs of laws/NamesCompareDecoded.bend
import Base
import ../src/value.bend as V
import ../main.bend as Ezjson
import ../src/lazy.bend as Lazy
import ../src/lex.bend as Lex
import ../src/parse.bend as Parse
import ../laws/NamesCompareDecoded.bend as Laws
import ../laws/SpansReadAsOwned.bend as L1
import ../laws/defs/CursorAndNumberRules.bend as D1
import ../laws/defs/GrammarDerivations.bend as D2
import ./lemmas/CanonicalValue.bend as M1
import ./lemmas/CharacterClasses.bend as M2
import ./lemmas/DenseTokens.bend as M3
import ./lemmas/KeySearch.bend as M4
import ./lemmas/LexemeOrder.bend as M5
import ./lemmas/LexerPunctuation.bend as M6
import ./lemmas/LexingPrintedText.bend as M7
import ./lemmas/OwnedParse.bend as M8
import ./lemmas/ParserReadsTokens.bend as M9
import ./lemmas/PrintFix.bend as M10
import ./lemmas/PrintedStringsParse.bend as M11
import ./lemmas/StringPieceLexing.bend as M12
import ./lemmas/StringTokens.bend as M13

# a one-member object is well-formed when its value is
law wf_one:
  for +val: V.Json
  for h: {V.wf(val) == True{} : Bool}
  {Lazy.stop(Bool, Bool.not(V.wf(val)), False{}, _u => V.wf.go(V.JNil{}, V.WObj{})) == True{} : Bool}

def wf_one(val, h):
  hl = Equal.sym(Bool, V.wf(val), True{}, h)
  %hl : {Lazy.stop(Bool, Bool.not(_), False{}, _u => V.wf.go(V.JNil{}, V.WObj{})) == True{} : Bool}
  {==}

# the character lexer on a one-member object whose name is spelled in pieces
law obj_lex:
  for +ps: List<&2, D2.Piece>
  for +val: V.Json
  for +h_ok: {D2.spell_ok(ps) == True{} : Bool}
  for +h_sc: {D1.scalars(D2.spelled(ps)) == True{} : Bool}
  for +h_wf: {V.wf(val) == True{} : Bool}
  {Lex.run(String.to_list("{\"" ++ D2.spell(ps) ++ "\":" ++ Ezjson.print(val) ++ "}"), Lex.Lex{Lex.Idle{}, [],
    []}) == M6.pend(V.JObj{V.JPair{D2.spelled(ps), val, V.JNil{}}}, []) : Lex.Lex}

def obj_lex(ps, val, h_ok, h_sc, h_wf):
  Equal.trans(Lex.Lex, Lex.run(String.to_list("{\"" ++ D2.spell(ps) ++ "\":" ++ Ezjson.print(val) ++ "}"),
    Lex.Lex{Lex.Idle{}, [], []}), Lex.run(String.to_list(D2.spell(ps) ++ "\":" ++ Ezjson.print(val) ++ "}"),
    Lex.Lex{Lex.Str{}, [], [Lex.TOpenObj{}]}), M6.pend(V.JObj{V.JPair{D2.spelled(ps), val, V.JNil{}}}, []),
        M13.seq("{\"",
    D2.spell(ps) ++ "\":" ++ Ezjson.print(val) ++ "}", Lex.Lex{Lex.Idle{}, [], []}, Lex.Lex{Lex.Str{}, [],
    [Lex.TOpenObj{}]}, {==}), Equal.trans(Lex.Lex,
    Lex.run(String.to_list(D2.spell(ps) ++ "\":" ++ Ezjson.print(val) ++ "}"), Lex.Lex{Lex.Str{}, [],
    [Lex.TOpenObj{}]}), Lex.run(String.to_list("\":" ++ Ezjson.print(val) ++ "}"), Lex.Lex{Lex.Str{},
    List.reverse.go(&2, Char, String.to_list(D2.spelled(ps)), []), [Lex.TOpenObj{}]}),
    M6.pend(V.JObj{V.JPair{D2.spelled(ps), val, V.JNil{}}}, []), M13.seq(D2.spell(ps),
        "\":" ++ Ezjson.print(val) ++ "}",
    Lex.Lex{Lex.Str{}, [], [Lex.TOpenObj{}]}, Lex.Lex{Lex.Str{}, List.reverse.go(&2, Char,
    String.to_list(D2.spelled(ps)), []), [Lex.TOpenObj{}]}, Equal.trans(Lex.Lex,
    Lex.run(String.to_list(D2.spell(ps)), Lex.Lex{Lex.Str{}, [], [Lex.TOpenObj{}]}),
    M2.lex.app(Lex.run(String.to_list(D2.spell(ps)), Lex.Lex{Lex.Str{}, [], []}), [Lex.TOpenObj{}]), Lex.Lex{Lex.Str{},
    List.reverse.go(&2, Char, String.to_list(D2.spelled(ps)), []), [Lex.TOpenObj{}]},
    M8.run_pass(String.to_list(D2.spell(ps)), Lex.Lex{Lex.Str{}, [], []}, [Lex.TOpenObj{}]), Equal.cong(Lex.Lex,
    Lex.Lex, zz => M2.lex.app(zz, [Lex.TOpenObj{}]), Lex.run(String.to_list(D2.spell(ps)), Lex.Lex{Lex.Str{}, [], []}),
    Lex.Lex{Lex.Str{}, List.reverse.go(&2, Char, String.to_list(D2.spelled(ps)), []), []}, M12.spell_lex(ps, h_ok,
    [])))), Equal.trans(Lex.Lex, Lex.run(String.to_list("\":" ++ Ezjson.print(val) ++ "}"), Lex.Lex{Lex.Str{},
    List.reverse.go(&2, Char, String.to_list(D2.spelled(ps)), []), [Lex.TOpenObj{}]}),
    Lex.run(String.to_list(Ezjson.print(val) ++ "}"), Lex.Lex{Lex.Idle{}, [],
    Lex.TColon{} <> Lex.TStr{Lex.text(List.reverse.go(&2, Char, String.to_list(D2.spelled(ps)),
    []))} <> [Lex.TOpenObj{}]}), M6.pend(V.JObj{V.JPair{D2.spelled(ps), val, V.JNil{}}}, []), M13.seq("\":",
    Ezjson.print(val) ++ "}", Lex.Lex{Lex.Str{}, List.reverse.go(&2, Char, String.to_list(D2.spelled(ps)), []),
    [Lex.TOpenObj{}]}, Lex.Lex{Lex.Idle{}, [], Lex.TColon{} <> Lex.TStr{Lex.text(List.reverse.go(&2, Char,
    String.to_list(D2.spelled(ps)), []))} <> [Lex.TOpenObj{}]}, {==}), Equal.trans(Lex.Lex,
    Lex.run(String.to_list(Ezjson.print(val) ++ "}"), Lex.Lex{Lex.Idle{}, [],
    Lex.TColon{} <> Lex.TStr{Lex.text(List.reverse.go(&2, Char, String.to_list(D2.spelled(ps)),
    []))} <> [Lex.TOpenObj{}]}), Lex.run(String.to_list("}"), M6.pend(val,
    Lex.TColon{} <> Lex.TStr{Lex.text(List.reverse.go(&2, Char, String.to_list(D2.spelled(ps)),
    []))} <> [Lex.TOpenObj{}])), M6.pend(V.JObj{V.JPair{D2.spelled(ps), val, V.JNil{}}}, []), M13.seq(Ezjson.print(val),
    "}", Lex.Lex{Lex.Idle{}, [], Lex.TColon{} <> Lex.TStr{Lex.text(List.reverse.go(&2, Char,
    String.to_list(D2.spelled(ps)), []))} <> [Lex.TOpenObj{}]}, M6.pend(val,
    Lex.TColon{} <> Lex.TStr{Lex.text(List.reverse.go(&2, Char, String.to_list(D2.spelled(ps)),
    []))} <> [Lex.TOpenObj{}]), M7.lexp(val, V.WVal{}, h_wf, Lex.TColon{} <> Lex.TStr{Lex.text(List.reverse.go(&2, Char,
    String.to_list(D2.spelled(ps)), []))} <> [Lex.TOpenObj{}])), Equal.trans(Lex.Lex, Lex.run(String.to_list("}"),
    M6.pend(val, Lex.TColon{} <> Lex.TStr{Lex.text(List.reverse.go(&2, Char, String.to_list(D2.spelled(ps)),
    []))} <> [Lex.TOpenObj{}])), Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, M5.tj(val,
    V.WVal{}), Lex.TColon{} <> Lex.TStr{Lex.text(List.reverse.go(&2, Char, String.to_list(D2.spelled(ps)),
    []))} <> [Lex.TOpenObj{}])}, M6.pend(V.JObj{V.JPair{D2.spelled(ps), val, V.JNil{}}}, []), M6.close(val, '}',
    Lex.TCloseObj{}, {==}, Lex.TColon{} <> Lex.TStr{Lex.text(List.reverse.go(&2, Char,
    String.to_list(D2.spelled(ps)), []))} <> [Lex.TOpenObj{}]), Equal.trans(Lex.Lex, Lex.Lex{Lex.Idle{}, [],
    Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, M5.tj(val, V.WVal{}),
    Lex.TColon{} <> Lex.TStr{Lex.text(List.reverse.go(&2, Char, String.to_list(D2.spelled(ps)),
    []))} <> [Lex.TOpenObj{}])}, Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, M5.tj(val,
    V.WVal{}), Lex.TColon{} <> Lex.TStr{D2.spelled(ps)} <> [Lex.TOpenObj{}])}, M6.pend(V.JObj{V.JPair{D2.spelled(ps),
    val, V.JNil{}}}, []), Equal.cong(String, Lex.Lex, zz => Lex.Lex{Lex.Idle{}, [],
    Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, M5.tj(val, V.WVal{}),
    Lex.TColon{} <> Lex.TStr{zz} <> [Lex.TOpenObj{}])}, Lex.text(List.reverse.go(&2, Char,
    String.to_list(D2.spelled(ps)), [])), D2.spelled(ps), M12.text_k(D2.spelled(ps))), Equal.trans(Lex.Lex,
    Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, M5.tj(val, V.WVal{}),
    Lex.TColon{} <> Lex.TStr{D2.spelled(ps)} <> [Lex.TOpenObj{}])}, Lex.Lex{Lex.Idle{}, [],
    Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, M5.tj(val, V.WVal{}),
    Lex.TColon{} <> Lex.TStr{M5.fixs(String.to_list(D2.spelled(ps)))} <> [Lex.TOpenObj{}])},
    M6.pend(V.JObj{V.JPair{D2.spelled(ps), val, V.JNil{}}}, []), Equal.cong(String, Lex.Lex, zz => Lex.Lex{Lex.Idle{},
    [], Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, M5.tj(val, V.WVal{}),
    Lex.TColon{} <> Lex.TStr{zz} <> [Lex.TOpenObj{}])}, D2.spelled(ps), M5.fixs(String.to_list(D2.spelled(ps))),
    Equal.sym(String, M5.fixs(String.to_list(D2.spelled(ps))), D2.spelled(ps), M11.fixs_id(D2.spelled(ps), h_sc))),
    Equal.cong(List<&2, Lex.Tok>, Lex.Lex, zz => Lex.Lex{Lex.Idle{}, [], zz}, Lex.TCloseObj{} <> List.reverse.go(&2,
    Lex.Tok, M5.tj(val, V.WVal{}),
        Lex.TColon{} <> Lex.TStr{M5.fixs(String.to_list(D2.spelled(ps)))} <> [Lex.TOpenObj{}]),
    List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok, M5.tj(val, V.WVal{}), [Lex.TCloseObj{}]),
    Lex.TColon{} <> Lex.TStr{M5.fixs(String.to_list(D2.spelled(ps)))} <> [Lex.TOpenObj{}]), Equal.sym(List<&2, Lex.Tok>,
    List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok, M5.tj(val, V.WVal{}), [Lex.TCloseObj{}]),
    Lex.TColon{} <> Lex.TStr{M5.fixs(String.to_list(D2.spelled(ps)))} <> [Lex.TOpenObj{}]),
    Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, M5.tj(val, V.WVal{}),
    Lex.TColon{} <> Lex.TStr{M5.fixs(String.to_list(D2.spelled(ps)))} <> [Lex.TOpenObj{}]), M12.rev_snoc_t(M5.tj(val,
    V.WVal{}), Lex.TCloseObj{},
    Lex.TColon{} <> Lex.TStr{M5.fixs(String.to_list(D2.spelled(ps)))} <> [Lex.TOpenObj{}]))))))))))

# parse on a one-member object whose name is spelled in pieces
law parse_obj:
  for +ps: List<&2, D2.Piece>
  for +val: V.Json
  for +h_ok: {D2.spell_ok(ps) == True{} : Bool}
  for +h_sc: {D1.scalars(D2.spelled(ps)) == True{} : Bool}
  for +h_wf: {V.wf(val) == True{} : Bool}
  for h_s: {D1.short("{\"" ++ D2.spell(ps) ++ "\":" ++ Ezjson.print(val) ++ "}") == True{} : Bool}
  {D1.own_m(Ezjson.parse("{\"" ++ D2.spell(ps) ++ "\":" ++ Ezjson.print(val) ++ "}")) ==
    Some{D1.fixv(D1.own(V.JObj{V.JPair{D2.spelled(ps), val, V.JNil{}}}))} : Maybe<&2, V.Json>}

def parse_obj(ps, val, h_ok, h_sc, h_wf, h_s):
  Equal.trans(Maybe<&2, V.Json>,
    D1.own_m(Parse.finish(Parse.run(Lex.tokens("{\"" ++ D2.spell(ps) ++ "\":" ++ Ezjson.print(val) ++ "}"),
    Parse.P{False{}, None{}, Nil{}}))),
    Parse.finish(M8.ownp(Parse.run(Lex.tokens("{\"" ++ D2.spell(ps) ++ "\":" ++ Ezjson.print(val) ++ "}"),
    Parse.P{False{}, None{}, Nil{}}))), Some{D1.fixv(D1.own(V.JObj{V.JPair{D2.spelled(ps), val, V.JNil{}}}))},
    M8.fin_own(Parse.run(Lex.tokens("{\"" ++ D2.spell(ps) ++ "\":" ++ Ezjson.print(val) ++ "}"), Parse.P{False{},
    None{}, Nil{}})), Equal.trans(Maybe<&2, V.Json>,
    Parse.finish(M8.ownp(Parse.run(Lex.tokens("{\"" ++ D2.spell(ps) ++ "\":" ++ Ezjson.print(val) ++ "}"),
    Parse.P{False{}, None{}, Nil{}}))),
    Parse.finish(Parse.run(M5.dens(Lex.tokens("{\"" ++ D2.spell(ps) ++ "\":" ++ Ezjson.print(val) ++ "}")),
    Parse.P{False{}, None{}, Nil{}})), Some{D1.fixv(D1.own(V.JObj{V.JPair{D2.spelled(ps), val, V.JNil{}}}))},
    Equal.cong(Parse.P, Maybe<&2, V.Json>, zz => Parse.finish(zz),
    M8.ownp(Parse.run(Lex.tokens("{\"" ++ D2.spell(ps) ++ "\":" ++ Ezjson.print(val) ++ "}"), Parse.P{False{}, None{},
    Nil{}})), Parse.run(M5.dens(Lex.tokens("{\"" ++ D2.spell(ps) ++ "\":" ++ Ezjson.print(val) ++ "}")),
    Parse.P{False{}, None{}, Nil{}}), M8.run_own(Lex.tokens("{\"" ++ D2.spell(ps) ++ "\":" ++ Ezjson.print(val) ++ "}"),
    Parse.P{False{}, None{}, Nil{}})), Equal.trans(Maybe<&2, V.Json>,
    Parse.finish(Parse.run(M5.dens(Lex.tokens("{\"" ++ D2.spell(ps) ++ "\":" ++ Ezjson.print(val) ++ "}")),
    Parse.P{False{}, None{}, Nil{}})), Parse.finish(Parse.run(M5.tj(V.JObj{V.JPair{D2.spelled(ps), val, V.JNil{}}},
    V.WVal{}), Parse.P{False{}, None{}, Nil{}})), Some{D1.fixv(D1.own(V.JObj{V.JPair{D2.spelled(ps), val,
    V.JNil{}}}))}, Equal.cong(List<&2, Lex.Tok>, Maybe<&2, V.Json>, zz => Parse.finish(Parse.run(zz, Parse.P{False{},
    None{}, Nil{}})), M5.dens(Lex.tokens("{\"" ++ D2.spell(ps) ++ "\":" ++ Ezjson.print(val) ++ "}")),
    M5.tj(V.JObj{V.JPair{D2.spelled(ps), val, V.JNil{}}}, V.WVal{}), Equal.trans(List<&2, Lex.Tok>,
    M5.dens(Lex.tokens("{\"" ++ D2.spell(ps) ++ "\":" ++ Ezjson.print(val) ++ "}")),
    M5.dens(Lex.finish(Lex.run(String.to_list("{\"" ++ D2.spell(ps) ++ "\":" ++ Ezjson.print(val) ++ "}"),
    Lex.Lex{Lex.Idle{}, [], []}))), M5.tj(V.JObj{V.JPair{D2.spelled(ps), val, V.JNil{}}}, V.WVal{}),
    M2.lexers_agree("{\"" ++ D2.spell(ps) ++ "\":" ++ Ezjson.print(val) ++ "}", h_s), Equal.trans(List<&2, Lex.Tok>,
    M5.dens(Lex.finish(Lex.run(String.to_list("{\"" ++ D2.spell(ps) ++ "\":" ++ Ezjson.print(val) ++ "}"),
    Lex.Lex{Lex.Idle{}, [], []}))), M5.dens(M5.tj(V.JObj{V.JPair{D2.spelled(ps), val, V.JNil{}}}, V.WVal{})),
    M5.tj(V.JObj{V.JPair{D2.spelled(ps), val, V.JNil{}}}, V.WVal{}), Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>,
    zz => M5.dens(zz), Lex.finish(Lex.run(String.to_list("{\"" ++ D2.spell(ps) ++ "\":" ++ Ezjson.print(val) ++ "}"),
    Lex.Lex{Lex.Idle{}, [], []})), M5.tj(V.JObj{V.JPair{D2.spelled(ps), val, V.JNil{}}}, V.WVal{}), Equal.trans(List<&2,
    Lex.Tok>, Lex.finish(Lex.run(String.to_list("{\"" ++ D2.spell(ps) ++ "\":" ++ Ezjson.print(val) ++ "}"),
    Lex.Lex{Lex.Idle{}, [], []})), Lex.finish(M6.pend(V.JObj{V.JPair{D2.spelled(ps), val, V.JNil{}}}, [])),
    M5.tj(V.JObj{V.JPair{D2.spelled(ps), val, V.JNil{}}}, V.WVal{}), Equal.cong(Lex.Lex, List<&2, Lex.Tok>,
    zz => Lex.finish(zz), Lex.run(String.to_list("{\"" ++ D2.spell(ps) ++ "\":" ++ Ezjson.print(val) ++ "}"),
    Lex.Lex{Lex.Idle{}, [], []}), M6.pend(V.JObj{V.JPair{D2.spelled(ps), val, V.JNil{}}}, []), obj_lex(ps, val, h_ok,
    h_sc, h_wf)), M11.fin_pend(V.JObj{V.JPair{D2.spelled(ps), val, V.JNil{}}}))),
    M3.dens_tj(V.JObj{V.JPair{D2.spelled(ps), val, V.JNil{}}}, V.WVal{})))), Equal.trans(Maybe<&2, V.Json>,
    Parse.finish(Parse.run(M5.tj(V.JObj{V.JPair{D2.spelled(ps), val, V.JNil{}}}, V.WVal{}), Parse.P{False{}, None{},
    Nil{}})), Some{M1.canon(V.JObj{V.JPair{D2.spelled(ps), val, V.JNil{}}}, V.WVal{})},
    Some{D1.fixv(D1.own(V.JObj{V.JPair{D2.spelled(ps), val, V.JNil{}}}))},
    M10.parse_tj(V.JObj{V.JPair{D2.spelled(ps), val, V.JNil{}}}, wf_one(val, h_wf)), Equal.cong(V.Json, Maybe<&2,
    V.Json>, zz => Some{zz}, M1.canon(V.JObj{V.JPair{D2.spelled(ps), val, V.JNil{}}}, V.WVal{}),
    D1.fixv(D1.own(V.JObj{V.JPair{D2.spelled(ps), val, V.JNil{}}})), M10.canon_fix(V.JObj{V.JPair{D2.spelled(ps),
    val, V.JNil{}}}, V.WVal{}, wf_one(val, h_wf)))))))

# get on a parsed value, once its owned form is known
law get_m_own:
  for mb: Maybe<&2, V.Json>
  for +key: String
  for +yy: V.Json
  for e: {D1.own_m(mb) == Some{yy} : Maybe<&2, V.Json>}
  {Laws.get_m(mb, key) == Some{Ezjson.get(yy, key)} : Maybe<&2, V.Json>}

def get_m_own(mb, key, yy, e):
  match mb:
    case None{}:
      M5.no({Laws.get_m(None{}, key) == Some{Ezjson.get(yy, key)} : Maybe<&2, V.Json>}, Equal.cong(Maybe<&2, V.Json>,
        Bool, zz => D1.is_some(zz), None{}, Some{yy}, e))
    case Some{+jj}:
      Equal.cong(V.Json, Maybe<&2, V.Json>, zz => Some{zz}, D1.own(Ezjson.get(jj, key)), Ezjson.get(yy, key),
        Equal.trans(V.Json, D1.own(Ezjson.get(jj, key)), Ezjson.get(D1.own(jj), key), Ezjson.get(yy, key),
        L1.get_same(jj, key), Equal.cong(V.Json, V.Json, zz => Ezjson.get(zz, key), D1.own(jj), yy,
        Equal.cong(Maybe<&2, V.Json>, V.Json, zz => M9.unsome(zz), Some{D1.own(jj)}, Some{yy}, e))))

# the lookup past a one-member object's only member
law fat:
  for bb: Bool
  for +key: String
  for +vv: V.Json
  {V.find.at(V.JNil{}, key, bb, vv) == Bool.pick(V.Json, bb, vv, V.JNull{}) : V.Json}

def fat(bb, _key, _vv):
  match bb:
    case True{}:
      {==}
    case False{}:
      {==}

def Laws.get_decoded(ps, val, key, h_ok, h_sc, h_wf, h_s):
  Equal.trans(Maybe<&2, V.Json>, Laws.get_m(Ezjson.parse("{\"" ++ D2.spell(ps) ++ "\":" ++ Ezjson.print(val) ++ "}"),
    key), Some{Ezjson.get(D1.fixv(D1.own(V.JObj{V.JPair{D2.spelled(ps), val, V.JNil{}}})), key)},
    Some{Bool.pick(V.Json, String.eq(D2.spelled(ps), key), D1.fixv(D1.own(val)), V.JNull{})},
    get_m_own(Ezjson.parse("{\"" ++ D2.spell(ps) ++ "\":" ++ Ezjson.print(val) ++ "}"), key,
    D1.fixv(D1.own(V.JObj{V.JPair{D2.spelled(ps), val, V.JNil{}}})), parse_obj(ps, val, h_ok, h_sc, h_wf, h_s)),
    Equal.cong(V.Json, Maybe<&2, V.Json>, zz => Some{zz},
    Ezjson.get(D1.fixv(D1.own(V.JObj{V.JPair{D2.spelled(ps), val, V.JNil{}}})), key), Bool.pick(V.Json,
    String.eq(D2.spelled(ps), key), D1.fixv(D1.own(val)), V.JNull{}), Equal.trans(V.Json, V.find.at(V.JNil{},
    key, V.find.eq(D1.fix_str(D2.spelled(ps)), key), D1.fixv(D1.own(val))), V.find.at(V.JNil{}, key,
    String.eq(D2.spelled(ps), key), D1.fixv(D1.own(val))), Bool.pick(V.Json, String.eq(D2.spelled(ps), key),
    D1.fixv(D1.own(val)), V.JNull{}), Equal.cong(Bool, V.Json, zz => V.find.at(V.JNil{}, key, zz,
    D1.fixv(D1.own(val))), V.find.eq(D1.fix_str(D2.spelled(ps)), key), String.eq(D2.spelled(ps), key),
    Equal.trans(Bool, V.find.eq.go(D1.fix_str(D2.spelled(ps)), key, True{}), V.find.eq.go(D2.spelled(ps), key,
    True{}), String.eq(D2.spelled(ps), key), Equal.cong(String, Bool, zz => V.find.eq.go(zz, key, True{}),
    D1.fix_str(D2.spelled(ps)), D2.spelled(ps), Equal.trans(String, D1.fix_str(D2.spelled(ps)),
    M5.fixs(String.to_list(D2.spelled(ps))), D2.spelled(ps), Equal.sym(String, M5.fixs(String.to_list(D2.spelled(ps))),
    D1.fix_str(D2.spelled(ps)), M10.fixs_eq(D2.spelled(ps))), M11.fixs_id(D2.spelled(ps), h_sc))),
    M4.find_str_eq(D2.spelled(ps), key))), fat(String.eq(D2.spelled(ps), key), key, D1.fixv(D1.own(val))))))
